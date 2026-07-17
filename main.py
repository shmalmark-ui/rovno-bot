"""
Ровно — личный анти-тревожный компаньон в Telegram.

Один пользователь. Не спам, не пилит. Работа с тревожно-поглощённым
типом привязанности через:

  1. Утренний check-in (адаптивный, по /awake или первому сообщению
     или по фолбэк-расписанию — чтобы бот не терял пользователя)
  2. Дневные касания (2-3 раза, привязаны к пробуждению)
  3. SOS-протокол — /help / кнопка. Таймер 20 мин прямо в чате,
     обновляемое сообщение. По окончании — «удалось? — победа
     в streak». Или новый круг.
  4. Ночной режим — /спать. Дыхание 4-7-8, релаксация, «убери телефон».
  5. Вечерний дневник (короткий → развёрнутый на волне 2)
  6. Волны 1 → 2 → 3 — бот сам предлагает расширить программу
     когда пользователь стабилен.
  7. Прогресс — streak побед, статистика недели, тренд тревоги.

Архитектура: aiogram 3.x + FastAPI + webhook. Скопирована с
agents-builder lead-bot: тот же StaticTelegramResolver (Timeweb VPS
имеет плохие маршруты к api.telegram.org, надо форсить рабочий IP),
тот же retry middleware, тот же owner-only фильтр.
"""
from __future__ import annotations

import asyncio
import json
import logging
import os
import secrets
import socket
from contextlib import asynccontextmanager
from datetime import date, datetime, time, timedelta, timezone
from pathlib import Path
from typing import Any

import aiohttp
import uvicorn
from aiogram import BaseMiddleware, Bot, Dispatcher, F
from aiogram.client.default import DefaultBotProperties
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.client.session.middlewares.base import BaseRequestMiddleware
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramNetworkError
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
    TelegramObject,
    Update,
)
from aiohttp.abc import AbstractResolver
from apscheduler.schedulers.asyncio import AsyncIOScheduler
from apscheduler.triggers.cron import CronTrigger
from fastapi import FastAPI, HTTPException, Request, Response

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("rovno")


# ---------- config ----------
BOT_TOKEN = os.environ["BOT_TOKEN"]
DATA_DIR = Path(os.environ.get("DATA_DIR", "/data"))
DATA_DIR.mkdir(parents=True, exist_ok=True)
STATE_FILE = DATA_DIR / "state.json"
_owner_env = os.environ.get("OWNER_CHAT_ID", "").strip()
OWNER_CHAT_ID_ENV: int | None = int(_owner_env) if _owner_env else None

WEBHOOK_BASE_URL = os.environ.get("WEBHOOK_BASE_URL", "https://rovno-bot.agents-builder.ru").rstrip("/")
WEBHOOK_PATH = "/webhook"
WEBHOOK_URL = f"{WEBHOOK_BASE_URL}{WEBHOOK_PATH}"

MSK = timezone(timedelta(hours=3))


# ---------- state ----------
def _default_state() -> dict[str, Any]:
    return {
        "owner_chat_id": None,
        "webhook_secret": None,
        "wave": 1,                # 1 | 2 | 3
        "streak": 0,              # consecutive "wins" — didn't message when triggered
        "total_wins": 0,
        "total_slips": 0,         # honest self-report: "wrote anyway"
        "last_awake_date": None,  # ISO date string
        "last_awake_hour": None,  # 0–23 hour of last /awake or first interaction
        "checkins": [],           # list of {ts, mood, anxiety, sleep_hours}
        "touches": [],            # list of {ts, level: "ok"|"rising"|"peak"}
        "journal": [],            # list of {date, trigger, action, truth}
        "panic_sessions": [],     # list of {started, ended, activity, wanted_to_write, cycles, won}
        "wave2_offered_at": None,
        "wave3_offered_at": None,
        # Reminder schedule (MSK). Bot uses awake-adaptive offsets when possible,
        # falling back to these clock times.
        "reminders": {
            "morning_fallback": "13:00",   # if no /awake by this time, prompt anyway
            "touch_offset_hours": [4, 8],  # after awake
            "evening_time": "22:30",       # can also shift based on awake
            "quiet_start": "01:30",        # don't touch him after this
            "quiet_end": "09:00",          # earliest morning touch
        },
    }


def load_state() -> dict[str, Any]:
    if STATE_FILE.exists():
        try:
            d = json.loads(STATE_FILE.read_text())
            # Fill in any keys added by newer versions
            defaults = _default_state()
            for k, v in defaults.items():
                d.setdefault(k, v)
            return d
        except Exception as e:
            log.warning("state file corrupted, starting fresh: %s", e)
    return _default_state()


def save_state() -> None:
    STATE_FILE.write_text(json.dumps(STATE, ensure_ascii=False, indent=2))


STATE = load_state()

# Persistent webhook secret
_webhook_secret_env = os.environ.get("WEBHOOK_SECRET", "").strip()
if _webhook_secret_env:
    STATE["webhook_secret"] = _webhook_secret_env
elif not STATE.get("webhook_secret"):
    STATE["webhook_secret"] = secrets.token_urlsafe(24)
    log.info("Generated new persistent webhook secret")
WEBHOOK_SECRET = STATE["webhook_secret"]

if OWNER_CHAT_ID_ENV is not None and STATE.get("owner_chat_id") != OWNER_CHAT_ID_ENV:
    log.info("OWNER_CHAT_ID env override → %s", OWNER_CHAT_ID_ENV)
    STATE["owner_chat_id"] = OWNER_CHAT_ID_ENV

save_state()


# ---------- utility ----------
def now_msk() -> datetime:
    return datetime.now(MSK)


def today_iso() -> str:
    return now_msk().date().isoformat()


def html_escape(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def in_quiet_hours() -> bool:
    """True if now is between quiet_start and quiet_end (night silence)."""
    r = STATE["reminders"]
    now = now_msk().time()
    qs = time.fromisoformat(r["quiet_start"])
    qe = time.fromisoformat(r["quiet_end"])
    if qs < qe:
        return qs <= now < qe
    # wraps midnight
    return now >= qs or now < qe


# ---------- telegram bot ----------
class RetryOnNetworkError(BaseRequestMiddleware):
    """Retry loop for all Bot API calls (VPS → api.telegram.org occasionally
    times out)."""

    def __init__(self, max_attempts: int = 5, base_sleep: float = 2.0):
        self.max_attempts = max_attempts
        self.base_sleep = base_sleep

    async def __call__(self, make_request, bot, method):
        last_exc: Exception | None = None
        for attempt in range(1, self.max_attempts + 1):
            try:
                return await make_request(bot, method)
            except TelegramNetworkError as e:
                last_exc = e
                if attempt < self.max_attempts:
                    delay = min(self.base_sleep * (1.6 ** (attempt - 1)), 12.0)
                    log.warning(
                        "%s: network timeout (attempt %d/%d), retry in %.1fs",
                        type(method).__name__, attempt, self.max_attempts, delay,
                    )
                    await asyncio.sleep(delay)
                else:
                    log.error(
                        "%s: gave up after %d attempts: %s",
                        type(method).__name__, self.max_attempts, e,
                    )
        assert last_exc is not None
        raise last_exc


class StaticTelegramResolver(AbstractResolver):
    """Force api.telegram.org → known-good IPs. See agents-builder bot for
    why: Timeweb VPS DNS returns .110 which is unreachable from that network."""

    _TELEGRAM_IPS = ["149.154.167.220", "149.154.166.110", "149.154.175.50"]

    async def resolve(self, host: str, port: int = 0, family: int = socket.AF_INET):
        if host == "api.telegram.org":
            return [
                {"hostname": host, "host": ip, "port": port,
                 "family": socket.AF_INET, "proto": 0, "flags": 0}
                for ip in self._TELEGRAM_IPS
            ]
        try:
            infos = socket.getaddrinfo(host, port, family=socket.AF_INET)
        except socket.gaierror:
            return []
        return [
            {"hostname": host, "host": addr[0], "port": addr[1],
             "family": family, "proto": 0, "flags": 0}
            for (_, _, _, _, addr) in infos
        ]

    async def close(self) -> None:
        pass


session = AiohttpSession(timeout=45)
session._connector_init["family"] = socket.AF_INET
session._connector_init["resolver"] = StaticTelegramResolver()
session.middleware(RetryOnNetworkError(max_attempts=5, base_sleep=2.5))
bot = Bot(
    token=BOT_TOKEN,
    default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    session=session,
)
dp = Dispatcher()


class OwnerOnlyMiddleware(BaseMiddleware):
    """Only the owner chat can use this bot. Anyone else is silently rejected."""

    async def __call__(self, handler, event: TelegramObject, data):
        owner = STATE.get("owner_chat_id")
        if isinstance(event, Message):
            chat_id = event.chat.id
            text = event.text or ""
            is_start = text.startswith("/start")
        elif isinstance(event, CallbackQuery):
            chat_id = event.message.chat.id if event.message else None
            is_start = False
        else:
            return await handler(event, data)
        if owner is None:
            if is_start:
                return await handler(event, data)
            log.info("rejected pre-bind message from chat_id=%s", chat_id)
            return None
        if chat_id == owner:
            return await handler(event, data)
        log.info("rejected foreign message from chat_id=%s (owner=%s)", chat_id, owner)
        return None


dp.message.middleware(OwnerOnlyMiddleware())
dp.callback_query.middleware(OwnerOnlyMiddleware())


# ---------- awake tracking ----------
def mark_awake(hour: int | None = None) -> None:
    """Called on /awake or on first interaction of the day.

    Sets today's awake hour so scheduler can compute touch offsets."""
    today = today_iso()
    prev_date = STATE.get("last_awake_date")
    if prev_date == today:
        # Already marked awake today — first call wins
        return
    h = hour if hour is not None else now_msk().hour
    STATE["last_awake_date"] = today
    STATE["last_awake_hour"] = h
    save_state()
    log.info("marked awake for %s at hour=%d", today, h)


def already_touched_today(key: str) -> bool:
    """Idempotency guard for scheduled reminders — don't fire the same reminder
    twice per day if bot restarts."""
    today = today_iso()
    return STATE.get(f"__touched_{key}") == today


def mark_touched(key: str) -> None:
    STATE[f"__touched_{key}"] = today_iso()
    save_state()


# ---------- keyboards ----------
def kb_home() -> InlineKeyboardMarkup:
    wave = STATE.get("wave", 1)
    rows = [
        [
            InlineKeyboardButton(text="🆘 Накатывает", callback_data="sos:start"),
            InlineKeyboardButton(text="😴 Ложусь", callback_data="sleep:start"),
        ],
        [
            InlineKeyboardButton(text="📝 Дневник", callback_data="journal:open"),
            InlineKeyboardButton(text="📊 Прогресс", callback_data="stats:open"),
        ],
        [
            InlineKeyboardButton(text="☀️ Я проснулся", callback_data="awake:mark"),
            InlineKeyboardButton(text="⚙️ Настройки", callback_data="settings:open"),
        ],
    ]
    if wave < 3:
        rows.append([InlineKeyboardButton(text=f"🌊 Волна {wave} / 3", callback_data="wave:info")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def kb_back_home() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="← Домой", callback_data="home")],
    ])


def kb_checkin_mood() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text=str(n), callback_data=f"ci:mood:{n}")
            for n in [1, 2, 3, 4, 5]
        ],
        [
            InlineKeyboardButton(text=str(n), callback_data=f"ci:mood:{n}")
            for n in [6, 7, 8, 9, 10]
        ],
        [InlineKeyboardButton(text="Пропустить", callback_data="ci:mood:skip")],
    ])


def kb_checkin_anxiety() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text=str(n), callback_data=f"ci:anxiety:{n}")
            for n in [1, 2, 3, 4, 5]
        ],
        [
            InlineKeyboardButton(text=str(n), callback_data=f"ci:anxiety:{n}")
            for n in [6, 7, 8, 9, 10]
        ],
        [InlineKeyboardButton(text="Пропустить", callback_data="ci:anxiety:skip")],
    ])


def kb_checkin_sleep() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="< 4 ч", callback_data="ci:sleep:3")],
        [InlineKeyboardButton(text="5 ч", callback_data="ci:sleep:5")],
        [InlineKeyboardButton(text="6 ч", callback_data="ci:sleep:6")],
        [InlineKeyboardButton(text="7 ч", callback_data="ci:sleep:7")],
        [InlineKeyboardButton(text="8+ ч", callback_data="ci:sleep:8")],
        [InlineKeyboardButton(text="Не помню", callback_data="ci:sleep:skip")],
    ])


def kb_touch() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="🟢 всё ровно", callback_data="touch:ok"),
            InlineKeyboardButton(text="🟡 накатывает", callback_data="touch:rising"),
        ],
        [InlineKeyboardButton(text="🔴 накрывает — SOS", callback_data="touch:peak")],
    ])


def kb_sos_activity() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🚶 Идти гулять", callback_data="sos:act:walk")],
        [InlineKeyboardButton(text="💪 Приседания / отжимания", callback_data="sos:act:physical")],
        [InlineKeyboardButton(text="🚿 Холодный душ", callback_data="sos:act:cold")],
        [InlineKeyboardButton(text="✍️ Написать в тетрадь", callback_data="sos:act:journal")],
        [InlineKeyboardButton(text="← Отмена", callback_data="home")],
    ])


def kb_sos_finish() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💪 Победа — отпустило", callback_data="sos:won")],
        [InlineKeyboardButton(text="🔄 Ещё 20 минут", callback_data="sos:again")],
        [InlineKeyboardButton(text="😞 Сорвался — написал", callback_data="sos:slip")],
    ])


def kb_sleep_options() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌬 Дыхание 4-7-8", callback_data="sleep:breathing")],
        [InlineKeyboardButton(text="🧘 Body scan", callback_data="sleep:bodyscan")],
        [InlineKeyboardButton(text="😵 Не могу уснуть — SOS", callback_data="sleep:panic")],
        [InlineKeyboardButton(text="← Домой", callback_data="home")],
    ])


# ---------- rendering ----------
def render_home() -> str:
    wave = STATE.get("wave", 1)
    streak = STATE.get("streak", 0)
    total_wins = STATE.get("total_wins", 0)
    last_ci = None
    if STATE["checkins"]:
        last_ci = STATE["checkins"][-1]

    lines = [
        f"🏠 <b>Ровно</b>",
        "",
        f"🌊 <b>Волна {wave} / 3</b>",
        f"💪 <b>{streak}</b> побед подряд · всего <b>{total_wins}</b>",
    ]
    if last_ci:
        try:
            ts = datetime.fromisoformat(last_ci["ts"]).astimezone(MSK)
            lines.append(f"📋 Последний check-in: <i>{ts.strftime('%d.%m %H:%M')}</i>")
        except Exception:
            pass
    lines.append("")
    lines.append("Выбери что нужно ↓")
    return "\n".join(lines)


HELP_TEXT = (
    "<b>Ровно · твой личный компаньон</b>\n\n"
    "Не даёт советов из воздуха. Даёт время до реакции. Считает победы. "
    "Помогает переждать 20 минут когда тревога накатывает.\n\n"
    "<b>Команды</b>\n"
    "/start — главный экран\n"
    "/help — SOS-протокол (20 минут)\n"
    "/awake — отметить что проснулся (запускает расписание дня)\n"
    "/сон — режим засыпания\n"
    "/log — быстро в дневник\n"
    "/stats — прогресс и статистика\n"
    "/settings — время напоминаний, вкл/выкл\n\n"
    "<b>Кнопки на главном экране</b>\n"
    "• 🆘 Накатывает — запускает SOS\n"
    "• 😴 Ложусь — режим сна\n"
    "• 📝 Дневник — запись за день\n"
    "• 📊 Прогресс — статистика\n"
    "• ☀️ Я проснулся — запускает расписание\n"
    "• ⚙️ Настройки — время, тишина, волны\n\n"
    "Волны 1 → 2 → 3 — постепенно усложняем программу. "
    "Начинаешь с волны 1 (20-минутный таймер), через 2 недели бот "
    "предложит волну 2 (полный дневник, 2 часа), потом волну 3 "
    "(правило 24 часа, NVC-шаблоны)."
)


# ---------- handlers ----------
@dp.message(CommandStart())
async def cmd_start(msg: Message) -> None:
    first_time = STATE.get("owner_chat_id") is None
    if first_time:
        STATE["owner_chat_id"] = msg.chat.id
        save_state()
        text = (
            "✅ <b>Бот подключён.</b>\n\n"
            f"Твой chat_id: <code>{msg.chat.id}</code>\n\n"
            "Я — <b>Ровно</b>. Персональный. Только для тебя. Никто "
            "другой сюда не пишет и меня не читает.\n\n"
            "Что я делаю:\n"
            "• 🆘 Даю время до реакции — таймер 20 мин когда накатывает\n"
            "• 📝 Веду дневник побед и триггеров\n"
            "• 😴 Помогаю засыпать когда не выходит\n"
            "• 📊 Показываю прогресс — тревога снижается со временем\n\n"
            "Начнём с волны 1 — только SOS-таймер и вечерний "
            "коротенький check-in. Через 2 недели предложу волну 2.\n\n"
            + render_home()
        )
    else:
        mark_awake()  # /start = сигнал что проснулся
        text = render_home()
    await msg.answer(text, reply_markup=kb_home())


@dp.message(Command("help"))
async def cmd_help(msg: Message) -> None:
    await start_sos(msg.chat.id, msg=msg)


@dp.message(Command("awake"))
async def cmd_awake(msg: Message) -> None:
    mark_awake()
    r = STATE["reminders"]
    first_touch = STATE["last_awake_hour"] + r["touch_offset_hours"][0]
    await msg.answer(
        f"☀️ Отметил. Проснулся в {STATE['last_awake_hour']:02d}:00.\n\n"
        f"Первое касание сегодня в {first_touch % 24:02d}:00 · "
        f"вечерний дневник — {r['evening_time']}.",
        reply_markup=kb_back_home(),
    )


@dp.message(Command("сон"))
@dp.message(Command("son"))
@dp.message(Command("sleep"))
async def cmd_sleep(msg: Message) -> None:
    await start_sleep_mode(msg.chat.id, msg=msg)


@dp.message(Command("log"))
async def cmd_log(msg: Message) -> None:
    await start_journal(msg.chat.id, msg=msg)


@dp.message(Command("stats"))
async def cmd_stats(msg: Message) -> None:
    await msg.answer(render_stats(), reply_markup=kb_back_home())


@dp.message(Command("settings"))
async def cmd_settings(msg: Message) -> None:
    await msg.answer(render_settings(), reply_markup=kb_settings())


@dp.callback_query(F.data == "home")
async def cb_home(cb: CallbackQuery) -> None:
    try:
        await cb.message.edit_text(render_home(), reply_markup=kb_home())
    except Exception:
        pass
    await cb.answer()


@dp.callback_query(F.data == "awake:mark")
async def cb_awake_mark(cb: CallbackQuery) -> None:
    mark_awake()
    await cb.answer("☀️ Отметил")
    try:
        await cb.message.edit_text(render_home(), reply_markup=kb_home())
    except Exception:
        pass


# ---------- SOS (panic protocol) ----------
async def start_sos(chat_id: int, msg: Message | None = None, cb: CallbackQuery | None = None) -> None:
    text = (
        "🆘 <b>Стоп.</b>\n\n"
        "Сейчас важно не написать ей.\n\n"
        "1. <b>Убери телефон в другую комнату</b> — прямо сейчас, "
        "физически. Не в карман. На тумбочку не считается.\n\n"
        "2. Выбери что делаешь эти 20 минут ↓"
    )
    if cb and cb.message:
        try:
            await cb.message.edit_text(text, reply_markup=kb_sos_activity())
        except Exception:
            await bot.send_message(chat_id, text, reply_markup=kb_sos_activity())
    else:
        await bot.send_message(chat_id, text, reply_markup=kb_sos_activity())


@dp.callback_query(F.data == "sos:start")
async def cb_sos_start(cb: CallbackQuery) -> None:
    await start_sos(cb.message.chat.id, cb=cb)
    await cb.answer()


ACTIVITY_LABELS = {
    "walk": "🚶 Гуляю",
    "physical": "💪 Отжимания / приседания",
    "cold": "🚿 Холодный душ",
    "journal": "✍️ Пишу в тетрадь",
}


@dp.callback_query(F.data.startswith("sos:act:"))
async def cb_sos_activity(cb: CallbackQuery) -> None:
    activity = cb.data.split(":", 2)[2]
    label = ACTIVITY_LABELS.get(activity, activity)

    # Create panic session record
    STATE["panic_sessions"].append({
        "started": now_msk().isoformat(),
        "activity": activity,
        "cycles": 1,
        "won": None,
    })
    save_state()

    # Start countdown message that we'll edit in place
    await run_countdown(cb.message.chat.id, label, minutes=20, cb=cb)


async def run_countdown(chat_id: int, activity_label: str, minutes: int, cb: CallbackQuery | None = None) -> None:
    """Countdown message that updates in place. Every minute for the first 5,
    then every 2, then final message. All from same message (edit_text)."""
    end_at = now_msk() + timedelta(minutes=minutes)

    def make_text(remaining_sec: int) -> str:
        m, s = divmod(max(0, remaining_sec), 60)
        return (
            f"⏳ <b>{m:02d}:{s:02d}</b> · {activity_label}\n\n"
            "Не проверяй чат. Не смотри её сторис. Ничего.\n"
            "Просто <b>оставайся в этой активности</b>.\n\n"
            "<i>Тревога — это волна. Она обязательно упадёт.</i>"
        )

    # Send initial message
    if cb and cb.message:
        try:
            await cb.message.edit_text(make_text(minutes * 60), reply_markup=None)
            message = cb.message
        except Exception:
            message = await bot.send_message(chat_id, make_text(minutes * 60))
    else:
        message = await bot.send_message(chat_id, make_text(minutes * 60))

    if cb:
        await cb.answer("Погнали 💪")

    # Update loop — sparse to avoid rate limits
    # Update at t-15, t-10, t-5, t-3, t-1 min marks
    marks = [minutes * 60 - k * 60 for k in [5, 10, 15]]
    marks = [m for m in marks if m > 0]
    marks.extend([180, 60])
    marks = sorted(set(marks), reverse=True)

    last_update = minutes * 60
    while True:
        remaining = int((end_at - now_msk()).total_seconds())
        if remaining <= 0:
            break
        # Find next mark
        try:
            next_mark = max(m for m in marks if m < last_update)
        except ValueError:
            next_mark = 0
        sleep_for = last_update - next_mark
        if sleep_for < 1:
            sleep_for = 1
        await asyncio.sleep(sleep_for)
        last_update = next_mark
        try:
            await message.edit_text(make_text(next_mark), reply_markup=None)
        except Exception as e:
            log.warning("countdown edit failed: %s", e)
        if next_mark == 0:
            break

    # Final prompt
    try:
        await message.edit_text(
            "⏰ <b>20 минут прошло.</b>\n\n"
            "Ну как?\n\n"
            "Если хочется писать так же сильно как в начале — "
            "запусти ещё круг. Часто второй проходит легче.\n\n"
            "Если отпустило — жми «Победа». Считаем в streak. 💪",
            reply_markup=kb_sos_finish(),
        )
    except Exception:
        await bot.send_message(chat_id, "20 минут прошло. Как ты?", reply_markup=kb_sos_finish())


@dp.callback_query(F.data == "sos:won")
async def cb_sos_won(cb: CallbackQuery) -> None:
    STATE["streak"] += 1
    STATE["total_wins"] += 1
    if STATE["panic_sessions"]:
        STATE["panic_sessions"][-1]["won"] = True
        STATE["panic_sessions"][-1]["ended"] = now_msk().isoformat()
    save_state()

    streak = STATE["streak"]
    text = (
        f"💪 <b>Победа. {streak}-я подряд.</b>\n\n"
        "Твой мозг только что записал: «Я не среагировал — и ничего "
        "не случилось». Это буквально переучивание нервной системы.\n\n"
        f"Всего побед: <b>{STATE['total_wins']}</b>"
    )
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer("💪")


@dp.callback_query(F.data == "sos:again")
async def cb_sos_again(cb: CallbackQuery) -> None:
    if STATE["panic_sessions"]:
        STATE["panic_sessions"][-1]["cycles"] += 1
    save_state()
    await run_countdown(cb.message.chat.id, "Второй круг", minutes=20, cb=cb)


@dp.callback_query(F.data == "sos:slip")
async def cb_sos_slip(cb: CallbackQuery) -> None:
    STATE["streak"] = 0  # reset streak
    STATE["total_slips"] += 1
    if STATE["panic_sessions"]:
        STATE["panic_sessions"][-1]["won"] = False
        STATE["panic_sessions"][-1]["ended"] = now_msk().isoformat()
    save_state()

    text = (
        "😌 <b>Записал.</b>\n\n"
        "Не удваивай. Ты уже написал — <b>не пиши четвёртое</b> "
        "«извини за флуд». Просто закрой чат.\n\n"
        "И самое главное: не самобичевание. Это будет. У всех. "
        "Считай что попробовал и учись на этом.\n\n"
        f"Триггер был какой? Запиши в дневник (/log) — через 2 недели "
        "увидишь паттерн."
    )
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer()


# ---------- Sleep mode ----------
async def start_sleep_mode(chat_id: int, msg: Message | None = None, cb: CallbackQuery | None = None) -> None:
    text = (
        "😴 <b>Готовимся ко сну.</b>\n\n"
        "Три шага прежде чем лечь:\n\n"
        "1. <b>Телефон в другую комнату.</b> Не рядом с подушкой. "
        "Если нужен будильник — оставь его в максимально далёкой "
        "точке кровати.\n\n"
        "2. <b>Никаких её сторис, чата, соцсетей последний час.</b> "
        "Это триггер номер один тревоги перед сном.\n\n"
        "3. Выбери одну технику ↓"
    )
    kb = kb_sleep_options()
    if cb and cb.message:
        try:
            await cb.message.edit_text(text, reply_markup=kb)
            return
        except Exception:
            pass
    await bot.send_message(chat_id, text, reply_markup=kb)


@dp.callback_query(F.data == "sleep:start")
async def cb_sleep_start(cb: CallbackQuery) -> None:
    await start_sleep_mode(cb.message.chat.id, cb=cb)
    await cb.answer()


@dp.callback_query(F.data == "sleep:breathing")
async def cb_sleep_breathing(cb: CallbackQuery) -> None:
    text = (
        "🌬 <b>Дыхание 4-7-8</b>\n\n"
        "Активирует парасимпатическую систему за 1-2 минуты. "
        "Проверено физиологически.\n\n"
        "<b>Как:</b>\n"
        "1. Ляг на спину.\n"
        "2. Выдохни весь воздух через рот.\n"
        "3. <b>Вдох носом на 4 счёта.</b>\n"
        "4. <b>Задержка на 7 счётов.</b>\n"
        "5. <b>Выдох ртом на 8 счётов</b> (со звуком, как через "
        "соломинку).\n"
        "6. Повтори <b>5 циклов</b>.\n\n"
        "После пятого цикла — не считай. Просто дыши нормально. "
        "Скорее всего провалишься в сон.\n\n"
        "<i>Если через 20 мин не заснул — не заставляй. Встань, "
        "попей воды, вернись через 10 мин.</i>"
    )
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer("🌬")


@dp.callback_query(F.data == "sleep:bodyscan")
async def cb_sleep_bodyscan(cb: CallbackQuery) -> None:
    text = (
        "🧘 <b>Body scan</b>\n\n"
        "Работает так: внимание идёт по телу сверху вниз. Ты "
        "не пытаешься расслабиться — только <b>замечаешь</b>. "
        "Тревога стихает потому что мозг занят одним делом.\n\n"
        "<b>Как:</b>\n"
        "Ляг. Закрой глаза. Медленно перечисляй в голове:\n\n"
        "• макушка головы — что чувствую?\n"
        "• лоб — напряжение? тепло?\n"
        "• челюсть — сжата?\n"
        "• шея, плечи, руки, ладони\n"
        "• грудь, живот, спина\n"
        "• таз, бёдра, колени\n"
        "• голени, ступни, пальцы ног\n\n"
        "На каждую точку — 3-5 медленных вдохов. Не пропускай.\n\n"
        "<i>Обычно люди засыпают на середине.</i>"
    )
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer("🧘")


@dp.callback_query(F.data == "sleep:panic")
async def cb_sleep_panic(cb: CallbackQuery) -> None:
    text = (
        "🌙 <b>Ночной SOS</b>\n\n"
        "Когда лёг и накатывает — не встаём в бой. Успокаиваем "
        "тело, а не спорим с мозгом.\n\n"
        "<b>Прямо сейчас, лёжа:</b>\n\n"
        "1. <b>Ощути 5 точек контакта с кроватью</b> — затылок, "
        "плечи, поясница, ягодицы, пятки. Задержись на каждой "
        "по 3 вдоха.\n\n"
        "2. <b>Считай выдохи</b> — только выдохи, до 30. Если "
        "сбился — начни с 1. Не с того места где сбился.\n\n"
        "3. <b>Дыхание 4-7-8, 5 циклов</b>.\n\n"
        "4. Если мысли всё равно бегут — назови вслух: «Это моя "
        "тревога. Она не про правду. Она сейчас пройдёт.»\n\n"
        "<i>Ты не должен уснуть за 5 минут. Ты должен снизить "
        "напряжение. Сон придёт когда придёт.</i>"
    )
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer()


# ---------- Journal / check-ins ----------
async def start_journal(chat_id: int, msg: Message | None = None) -> None:
    wave = STATE.get("wave", 1)
    if wave == 1:
        # Wave 1 — just quick evening feeling
        text = (
            "📝 <b>Дневник — короткий</b>\n\n"
            "На волне 1 достаточно быстро отметить настроение и тревогу.\n\n"
            "Настроение сегодня? (1 — днище, 10 — прекрасно)"
        )
        kb = kb_checkin_mood()
    else:
        text = (
            "📝 <b>Дневник — вечерний</b>\n\n"
            "Три быстрых вопроса:\n"
            "1. Настроение (1-10)?\n"
            "2. Уровень тревоги (1-10)?\n"
            "3. Что триггернуло сегодня? — напиши текстом позже\n\n"
            "Начнём с настроения ↓"
        )
        kb = kb_checkin_mood()
    if msg:
        await msg.answer(text, reply_markup=kb)
    else:
        await bot.send_message(chat_id, text, reply_markup=kb)


@dp.callback_query(F.data == "journal:open")
async def cb_journal_open(cb: CallbackQuery) -> None:
    try:
        await cb.message.edit_text(
            "📝 <b>Дневник</b>\n\nНастроение сегодня? (1 — днище, 10 — прекрасно)",
            reply_markup=kb_checkin_mood(),
        )
    except Exception:
        pass
    await cb.answer()


# Store partial check-in in a temp key inside state
def _partial_checkin() -> dict:
    return STATE.setdefault("__partial_ci", {})


@dp.callback_query(F.data.startswith("ci:mood:"))
async def cb_ci_mood(cb: CallbackQuery) -> None:
    val = cb.data.split(":", 2)[2]
    p = _partial_checkin()
    if val != "skip":
        p["mood"] = int(val)
    save_state()
    text = "😰 <b>Тревога сегодня?</b> (1 — ноль, 10 — накрывает)"
    try:
        await cb.message.edit_text(text, reply_markup=kb_checkin_anxiety())
    except Exception:
        pass
    await cb.answer()


@dp.callback_query(F.data.startswith("ci:anxiety:"))
async def cb_ci_anxiety(cb: CallbackQuery) -> None:
    val = cb.data.split(":", 2)[2]
    p = _partial_checkin()
    if val != "skip":
        p["anxiety"] = int(val)
    save_state()
    text = "😴 <b>Сколько удалось поспать?</b>"
    try:
        await cb.message.edit_text(text, reply_markup=kb_checkin_sleep())
    except Exception:
        pass
    await cb.answer()


@dp.callback_query(F.data.startswith("ci:sleep:"))
async def cb_ci_sleep(cb: CallbackQuery) -> None:
    val = cb.data.split(":", 2)[2]
    p = _partial_checkin()
    if val != "skip":
        p["sleep_hours"] = int(val)
    p["ts"] = now_msk().isoformat()
    STATE["checkins"].append(dict(p))
    STATE.pop("__partial_ci", None)
    save_state()

    text = "✅ <b>Записал.</b>\n\nЕсли хочешь — напиши текстом что триггернуло за день. Просто в чат."
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer()


# ---------- Touches (day check-ins) ----------
@dp.callback_query(F.data.startswith("touch:"))
async def cb_touch(cb: CallbackQuery) -> None:
    level = cb.data.split(":", 1)[1]
    STATE["touches"].append({
        "ts": now_msk().isoformat(),
        "level": level,
    })
    save_state()

    if level == "peak":
        await start_sos(cb.message.chat.id, cb=cb)
    else:
        msg = {
            "ok": "🟢 Отлично. Отметил.",
            "rising": "🟡 Отметил. Помни — правило 20 минут. Не пиши сразу.",
        }[level]
        try:
            await cb.message.edit_text(msg, reply_markup=kb_back_home())
        except Exception:
            pass
    await cb.answer()


# ---------- Stats ----------
def render_stats() -> str:
    streak = STATE.get("streak", 0)
    wins = STATE.get("total_wins", 0)
    slips = STATE.get("total_slips", 0)
    wave = STATE.get("wave", 1)

    # Anxiety trend — average of last 7 check-ins vs previous 7
    checkins = STATE.get("checkins", [])
    trend_line = ""
    if len(checkins) >= 4:
        recent = [c.get("anxiety") for c in checkins[-7:] if c.get("anxiety") is not None]
        older = [c.get("anxiety") for c in checkins[-14:-7] if c.get("anxiety") is not None]
        if recent and older:
            r_avg = sum(recent) / len(recent)
            o_avg = sum(older) / len(older)
            delta = r_avg - o_avg
            arrow = "↓" if delta < -0.3 else ("↑" if delta > 0.3 else "→")
            trend_line = f"📉 Средняя тревога: <b>{r_avg:.1f}</b> {arrow} (было {o_avg:.1f})\n"

    # Sleep average
    sleep_vals = [c.get("sleep_hours") for c in checkins[-14:] if c.get("sleep_hours") is not None]
    sleep_line = ""
    if sleep_vals:
        s_avg = sum(sleep_vals) / len(sleep_vals)
        sleep_line = f"😴 Средний сон за 2 нед: <b>{s_avg:.1f} ч</b>\n"

    # Panic sessions count
    sessions = STATE.get("panic_sessions", [])
    total_sessions = len(sessions)

    return (
        f"📊 <b>Прогресс</b>\n\n"
        f"🌊 Волна <b>{wave}</b> / 3\n"
        f"💪 Streak побед: <b>{streak}</b>\n"
        f"💪 Всего побед: <b>{wins}</b>\n"
        f"😞 Срывов: <b>{slips}</b>\n"
        f"🆘 SOS-сессий: <b>{total_sessions}</b>\n\n"
        f"{trend_line}"
        f"{sleep_line}\n"
        "<i>Тревога снижается медленно и с колебаниями. "
        "Смотри на 2-недельный тренд, не на день.</i>"
    )


@dp.callback_query(F.data == "stats:open")
async def cb_stats_open(cb: CallbackQuery) -> None:
    try:
        await cb.message.edit_text(render_stats(), reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer()


# ---------- Wave management ----------
@dp.callback_query(F.data == "wave:info")
async def cb_wave_info(cb: CallbackQuery) -> None:
    wave = STATE.get("wave", 1)
    descriptions = {
        1: (
            "🌊 <b>Волна 1</b> — фундамент.\n\n"
            "Что делаем:\n"
            "• SOS-таймер 20 мин когда накатывает\n"
            "• Короткий вечерний check-in\n"
            "• Дыхание 4-7-8 перед сном\n"
            "• Пауза 3 сек перед реакцией на шутку\n\n"
            "Ничего сложного. Задача — просто удержаться."
        ),
        2: (
            "🌊 <b>Волна 2</b> — расширяем.\n\n"
            "К волне 1 добавляется:\n"
            "• Полный дневник вечером (триггер / что сделал / что оказалось правдой)\n"
            "• Расширенный SOS-таймер до 2 часов\n"
            "• Еженедельный обзор в воскресенье"
        ),
        3: (
            "🌊 <b>Волна 3</b> — глубина.\n\n"
            "К волнам 1-2 добавляется:\n"
            "• Правило 24 часа — SOS-таймер расширяется до суток\n"
            "• NVC-шаблоны для важных разговоров\n"
            "• Готовность к терапии"
        ),
    }
    text = descriptions.get(wave, "?")
    try:
        await cb.message.edit_text(text, reply_markup=kb_back_home())
    except Exception:
        pass
    await cb.answer()


# ---------- Settings ----------
def kb_settings() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🌊 Сменить волну", callback_data="settings:wave")],
        [InlineKeyboardButton(text="⏰ Расписание", callback_data="settings:schedule")],
        [InlineKeyboardButton(text="🔇 Тишина ночью", callback_data="settings:quiet")],
        [InlineKeyboardButton(text="← Домой", callback_data="home")],
    ])


def render_settings() -> str:
    r = STATE["reminders"]
    wave = STATE.get("wave", 1)
    return (
        "⚙️ <b>Настройки</b>\n\n"
        f"🌊 Волна: <b>{wave} / 3</b>\n"
        f"☀️ Утренний фолбэк: <b>{r['morning_fallback']}</b>\n"
        f"⏰ Касания через: <b>+{r['touch_offset_hours'][0]}ч, +{r['touch_offset_hours'][1]}ч</b> после awake\n"
        f"🌙 Вечерний дневник: <b>{r['evening_time']}</b>\n"
        f"🔇 Тишина: <b>{r['quiet_start']} — {r['quiet_end']}</b>"
    )


@dp.callback_query(F.data == "settings:open")
async def cb_settings_open(cb: CallbackQuery) -> None:
    try:
        await cb.message.edit_text(render_settings(), reply_markup=kb_settings())
    except Exception:
        pass
    await cb.answer()


@dp.callback_query(F.data == "settings:wave")
async def cb_settings_wave(cb: CallbackQuery) -> None:
    current = STATE.get("wave", 1)
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(
            text=f"{'✅' if current == n else '⚪'} Волна {n}",
            callback_data=f"settings:set_wave:{n}",
        )] for n in [1, 2, 3]
    ] + [[InlineKeyboardButton(text="← Назад", callback_data="settings:open")]])
    try:
        await cb.message.edit_text(
            f"🌊 <b>Смена волны</b>\n\nСейчас: <b>{current}</b>",
            reply_markup=kb,
        )
    except Exception:
        pass
    await cb.answer()


@dp.callback_query(F.data.startswith("settings:set_wave:"))
async def cb_settings_set_wave(cb: CallbackQuery) -> None:
    new_wave = int(cb.data.split(":")[-1])
    STATE["wave"] = new_wave
    save_state()
    await cb.answer(f"🌊 Волна {new_wave}")
    try:
        await cb.message.edit_text(render_settings(), reply_markup=kb_settings())
    except Exception:
        pass


# ---------- Free text = journal note ----------
@dp.message(F.text & ~F.text.startswith("/"))
async def any_text(msg: Message) -> None:
    """Свободный текст = запись в дневник (если сегодня уже был check-in)
    или регистрация как «проснулся» + начать check-in."""
    today = today_iso()

    # First interaction of the day → mark awake
    if STATE.get("last_awake_date") != today:
        mark_awake()
        await msg.answer(
            "☀️ Отметил что проснулся. Хочешь короткий check-in?\n\n"
            "(нажми «📝 Дневник» когда готов)",
            reply_markup=kb_home(),
        )
        return

    # Otherwise treat as journal note
    STATE["journal"].append({
        "date": today,
        "ts": now_msk().isoformat(),
        "trigger": msg.text[:2000],  # truncate
        "action": "",
        "truth": "",
    })
    save_state()
    await msg.answer(
        "📝 Записал в дневник. Через 2 недели увидим паттерн.",
        reply_markup=kb_back_home(),
    )


# ---------- Scheduler ----------
scheduler = AsyncIOScheduler(timezone="Europe/Moscow")


async def scheduled_morning_fallback() -> None:
    """If user didn't send /awake or any message by morning_fallback time,
    prompt anyway."""
    if in_quiet_hours():
        return
    if already_touched_today("morning_fallback"):
        return
    if STATE.get("last_awake_date") == today_iso():
        # He's already interacted today
        return
    chat_id = STATE.get("owner_chat_id")
    if not chat_id:
        return
    mark_touched("morning_fallback")
    try:
        await bot.send_message(
            chat_id,
            "☀️ Привет. Ты проснулся? Как ты?\n\n"
            "Если да — жми ниже, запущу расписание дня.",
            reply_markup=kb_home(),
        )
    except Exception as e:
        log.warning("morning fallback send failed: %s", e)


async def scheduled_touch(offset_index: int) -> None:
    """Send a "touch" prompt N hours after awake."""
    if in_quiet_hours():
        return
    key = f"touch_{offset_index}"
    if already_touched_today(key):
        return
    if STATE.get("last_awake_date") != today_iso():
        return  # not yet awake today
    awake_h = STATE.get("last_awake_hour")
    if awake_h is None:
        return
    r = STATE["reminders"]
    try:
        offset_h = r["touch_offset_hours"][offset_index]
    except IndexError:
        return
    target_h = (awake_h + offset_h) % 24
    if now_msk().hour < target_h:
        return  # not yet time
    chat_id = STATE.get("owner_chat_id")
    if not chat_id:
        return
    mark_touched(key)
    try:
        await bot.send_message(
            chat_id,
            "👋 Как накатывает?",
            reply_markup=kb_touch(),
        )
    except Exception as e:
        log.warning("touch send failed: %s", e)


async def scheduled_evening() -> None:
    """Evening journal prompt."""
    if in_quiet_hours():
        return
    if already_touched_today("evening"):
        return
    chat_id = STATE.get("owner_chat_id")
    if not chat_id:
        return
    mark_touched("evening")
    try:
        await bot.send_message(
            chat_id,
            "🌙 <b>Вечерний дневник</b>\n\nКак прошёл день?",
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                [InlineKeyboardButton(text="📝 Записать", callback_data="journal:open")],
                [InlineKeyboardButton(text="Пропустить", callback_data="home")],
            ]),
        )
    except Exception as e:
        log.warning("evening send failed: %s", e)


async def scheduled_wave_check() -> None:
    """Every day at 20:00 MSK — if user has been on wave 1 for 14+ days with
    stable engagement, offer wave 2."""
    chat_id = STATE.get("owner_chat_id")
    if not chat_id:
        return
    wave = STATE.get("wave", 1)
    if wave >= 3:
        return
    # Track first interaction date
    first_ci = STATE["checkins"][0] if STATE["checkins"] else None
    if not first_ci:
        return
    try:
        first_date = datetime.fromisoformat(first_ci["ts"]).astimezone(MSK).date()
    except Exception:
        return
    days_active = (now_msk().date() - first_date).days

    if wave == 1 and days_active >= 14 and STATE.get("wave2_offered_at") is None:
        STATE["wave2_offered_at"] = today_iso()
        save_state()
        try:
            await bot.send_message(
                chat_id,
                "🌊 <b>Ты 2 недели со мной.</b>\n\n"
                f"Побед: <b>{STATE['total_wins']}</b>. "
                "Готов добавить <b>волну 2</b>?\n\n"
                "На волне 2 добавляется полный вечерний дневник "
                "(триггер / что сделал / что оказалось правдой), "
                "и SOS-таймер расширяется с 20 мин до 2 часов.",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                    [InlineKeyboardButton(text="💪 Погнали", callback_data="settings:set_wave:2")],
                    [InlineKeyboardButton(text="⏳ Попозже", callback_data="home")],
                ]),
            )
        except Exception as e:
            log.warning("wave check send failed: %s", e)

    elif wave == 2 and days_active >= 35 and STATE.get("wave3_offered_at") is None:
        STATE["wave3_offered_at"] = today_iso()
        save_state()
        try:
            await bot.send_message(
                chat_id,
                "🌊 <b>Готов к волне 3?</b>\n\n"
                "На волне 3 — правило 24 часа, NVC-шаблоны для "
                "разговоров с ней, готовность к терапии.",
                reply_markup=InlineKeyboardMarkup(inline_keyboard=[
                    [InlineKeyboardButton(text="💪 Погнали", callback_data="settings:set_wave:3")],
                    [InlineKeyboardButton(text="⏳ Попозже", callback_data="home")],
                ]),
            )
        except Exception as e:
            log.warning("wave3 check send failed: %s", e)


def setup_scheduler() -> None:
    """Runs every 15 minutes and lets each scheduled fn decide if it should
    fire. This keeps logic simple even when user's schedule shifts daily."""
    scheduler.add_job(
        scheduled_morning_fallback,
        CronTrigger(minute="*/15", hour="12-16"),  # window when we prompt if idle
        id="morning_fallback",
    )
    scheduler.add_job(
        lambda: scheduled_touch(0),
        CronTrigger(minute="*/15", hour="*"),
        id="touch_0",
    )
    scheduler.add_job(
        lambda: scheduled_touch(1),
        CronTrigger(minute="*/15", hour="*"),
        id="touch_1",
    )
    scheduler.add_job(
        scheduled_evening,
        CronTrigger(minute="0,15,30,45", hour="22-23"),
        id="evening",
    )
    scheduler.add_job(
        scheduled_wave_check,
        CronTrigger(hour=20, minute=0),
        id="wave_check",
    )
    scheduler.start()
    log.info("Scheduler started (%d jobs)", len(scheduler.get_jobs()))


# ---------- webhook setup ----------
async def _try_set_webhook() -> bool:
    try:
        await asyncio.wait_for(
            bot.set_webhook(
                url=WEBHOOK_URL,
                secret_token=WEBHOOK_SECRET,
                drop_pending_updates=True,
                allowed_updates=dp.resolve_used_update_types(),
            ),
            timeout=25.0,
        )
        return True
    except Exception as e:
        log.warning("set_webhook failed: %s: %s", type(e).__name__, str(e)[:120])
        return False


async def _background_webhook_setup() -> None:
    while True:
        await asyncio.sleep(60)
        log.info("Background webhook setup attempt...")
        if await _try_set_webhook():
            log.info("Webhook registered in background: %s", WEBHOOK_URL)
            return


@asynccontextmanager
async def lifespan(_: FastAPI):
    log.info("Lifespan start. Webhook target: %s", WEBHOOK_URL)
    if os.environ.get("SKIP_SETWEBHOOK", "").strip() in ("1", "true", "yes"):
        log.info("SKIP_SETWEBHOOK set — not touching webhook")
    else:
        success = False
        for attempt in range(1, 4):
            if await _try_set_webhook():
                log.info("Webhook registered on attempt %d: %s", attempt, WEBHOOK_URL)
                success = True
                break
            if attempt < 3:
                await asyncio.sleep(min(5 * attempt, 15))
        if not success:
            log.warning("Initial webhook setup failed — background retry loop")
            asyncio.create_task(_background_webhook_setup())
    setup_scheduler()
    log.info(
        "Rovno ready. owner=%s wave=%s streak=%d",
        STATE.get("owner_chat_id"), STATE.get("wave"), STATE.get("streak", 0),
    )
    yield
    log.info("Shutting down — removing webhook")
    try:
        scheduler.shutdown(wait=False)
    except Exception:
        pass
    try:
        await asyncio.wait_for(bot.delete_webhook(), timeout=10.0)
    except Exception:
        log.exception("delete_webhook failed on shutdown")
    try:
        await session.close()
    except Exception:
        pass


app = FastAPI(
    title="rovno personal bot",
    docs_url=None,
    redoc_url=None,
    lifespan=lifespan,
)


@app.post(WEBHOOK_PATH)
async def telegram_webhook(request: Request) -> Response:
    secret = request.headers.get("X-Telegram-Bot-Api-Secret-Token", "")
    if secret != WEBHOOK_SECRET:
        log.warning("Webhook request with bad secret (len=%d)", len(secret))
        raise HTTPException(status_code=403, detail="bad secret")
    try:
        data = await request.json()
    except Exception:
        raise HTTPException(status_code=400, detail="bad json")
    update = Update.model_validate(data, context={"bot": bot})
    asyncio.create_task(_process_update(update))
    return Response(status_code=200)


async def _process_update(update: Update) -> None:
    try:
        await dp.feed_update(bot, update)
    except Exception:
        log.exception("feed_update failed for update_id=%s", update.update_id)


@app.get("/health")
async def health():
    return {
        "status": "ok",
        "bound": STATE.get("owner_chat_id") is not None,
        "wave": STATE.get("wave"),
        "streak": STATE.get("streak"),
        "total_wins": STATE.get("total_wins"),
        "checkins_count": len(STATE.get("checkins", [])),
        "webhook_url": WEBHOOK_URL,
    }


def main() -> None:
    log.info("Starting Rovno bot on :8000")
    config = uvicorn.Config(
        app,
        host="0.0.0.0",
        port=8000,
        log_level="info",
        access_log=False,
        proxy_headers=True,
        forwarded_allow_ips="*",
    )
    server = uvicorn.Server(config)
    asyncio.run(server.serve())


if __name__ == "__main__":
    main()
