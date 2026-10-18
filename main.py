import base64
import collections
import importlib.util
import io
import json
import math
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.request
import wave
import tkinter as tk
from tkinter import scrolledtext, ttk
from pathlib import Path

# Wymuszamy X11 (na Wayland przez XWayland) - przezroczystość i przeciąganie okna bez ramki
os.environ.setdefault("SDL_VIDEODRIVER", "x11")

import numpy as np
import sounddevice as sd
import speech_recognition as sr

try:
    import mss
    from PIL import Image
    MSS = getattr(mss, "MSS", None) or mss.mss
    SCREEN_AVAILABLE = True
except ImportError:
    SCREEN_AVAILABLE = False
    print("[ekran] Brak bibliotek - zainstaluj: pip install mss pillow")

try:
    import cv2
    CV2_AVAILABLE = True
except ImportError:
    CV2_AVAILABLE = False

try:
    import pygame
    from pygame.locals import DOUBLEBUF, OPENGL, NOFRAME
    import live2d

    LIVE2D_AVAILABLE = hasattr(live2d, "Model")
    if not LIVE2D_AVAILABLE:
        print("[live2d] Brak klasy live2d.Model - zaktualizuj: pip install -U live2d-py")
except ImportError as _e:
    LIVE2D_AVAILABLE = False
    print(f"[live2d] Brak biblioteki: {_e}")

# ======================= USTAWIENIA =======================
MODEL_PATH = "assets/FREE Chibi Model (D_maf)/Чиби Эмми D_maf.model3.json"
OLLAMA_MODEL = "qwen2.5:7b"
OLLAMA_OPTIONS = {"temperature": 0.8, "num_predict": 160, "num_ctx": 4096}
VISION_MODEL = "llava:latest"     # ollama pull llava
DEFAULT_LANG = "pl"               # pl / en / ja
OVERLAY_TITLE = "Chibi Emmy Live2D"
OVERLAY_W, OVERLAY_H = 400, 500
OVERLAY_START_POS = (150, 150)
TRANSPARENT = False               # klawisz T przełącza przezroczystość
ALWAYS_ON_TOP = True              # wymaga wmctrl
USE_EDGE = True                   # ładne głosy edge-tts (internet); False = lokalny Piper/espeak
EDGE_OK = USE_EDGE and importlib.util.find_spec("edge_tts") is not None

# --- cel i asystent produktywności ---
GOAL_FILE = Path(__file__).resolve().parent / "cel.txt"
GOAL_MAX_CHARS = 1500
GOAL_TEMPLATE = (
    "CEL: (wpisz tutaj swój obecny cel, np. Skończyć moduł logowania do piątku)\n"
    "KROKI: (opcjonalnie: kolejne małe kroki)\n"
    "ROZPRASZACZE: YouTube, Reddit, Discord, Facebook, Netflix\n"
    "NOTATKI: (opcjonalnie: np. przerwa co 50 minut)\n"
)
GOAL_KEYS = {"CEL", "GOAL", "目標"}
KNOWN_KEYS = GOAL_KEYS | {"KROKI", "STEPS", "ROZPRASZACZE", "DISTRACTIONS", "NOTATKI", "NOTES"}

WINDOW_TOOLS = True               # lista i zamykanie okien (wymaga wmctrl, X11/XWayland)
PROTECTED_WINDOWS = ["emmy", "lokalna anime waifu", "pycharm", "aurola"]   # małe litery; tych nie zamknie
CONFIRM_TIMEOUT = 30              # s na potwierdzenie zamknięcia okna

# --- nasłuch (VAD) ---
SAMPLE_RATE = 16000
BLOCK = 512                       # 32 ms
BLOCK_S = BLOCK / SAMPLE_RATE
MIN_THRESHOLD = 300               # minimalny próg głośności (skala int16)
NOISE_FACTOR = 3.0                # próg = szum otoczenia * tyle
START_BLOCKS = 3                  # tyle głośnych bloków pod rząd = początek mowy
PRE_ROLL_BLOCKS = 10              # ile nagrania zachować sprzed początku mowy
END_SILENCE = 1.0                 # s ciszy kończące wypowiedź
MIN_SPEECH = 0.3                  # s - krótsze dźwięki ignorujemy
MAX_UTTERANCE = 20.0              # s - maksymalna długość jednej wypowiedzi
MUTE_AFTER_SPEECH = 0.8           # s wyciszenia po jej mówieniu (pogłos)

# --- sama zaczyna rozmowę ---
IDLE_MIN, IDLE_MAX = 120, 300     # s ciszy przed zagadaniem (x2 po każdym braku odpowiedzi, max x8)
REPLY_WAIT = 45                   # s czekania na odpowiedź po zagadaniu

# --- ekran / kamerka ---
SCREEN_MIN_DELAY, SCREEN_MAX_DELAY = 180, 420   # s między sprawdzeniami ekranu
USE_WEBCAM = False
WEBCAM_CHANCE = 0.3
WEBCAM_INDEX = 0

VOICE_DIR = Path.home() / ".local" / "share" / "piper"
_voice_lock = threading.Lock()

# ======================= PROMPTY =======================
COACH_RULES = (
    "You are also senpai's productivity companion. Help him move toward his goal: encourage him, suggest one "
    "small next step, notice distractions, remind him about short breaks. Be supportive, never preachy, "
    "never repetitive.\n"
    "CLOSING WINDOWS: you can close windows, but ONLY when senpai asks you to, or when an open window is "
    "clearly a distraction from his goal and you offer to close it. Ask first (for example: \"Should I close "
    "X?\") and put this tag at the very end of that reply: [[CLOSE: part of the window title]]. Use only "
    "titles from the open-windows list. The system then asks senpai to confirm. Never use the tag in any "
    "other case, and never say that a window is already closed - the system does that."
)

IDLE_TOPICS = [
    "ask how his day is going",
    "ask what he is doing right now",
    "ask about his favorite anime or game",
    "tell a tiny cute joke",
    "ask if he needs a break, some water or a snack",
]
IDLE_TOPICS_GOAL = [
    "ask how the work on his goal is going",
    "suggest one tiny next step toward his goal",
    "remind him to take a short break, stretch or drink water",
    "ask whether he is stuck on something and offer to think it through",
    "cheer him on about his goal",
]
IDLE_HINT = ("[Senpai has been silent for a while. Start a conversation yourself: {topic}. "
             "Reply ONLY in {lang}, as Emmy, 1-2 short sentences, end with one simple question.]")
SCREEN_HINT = ("[You can see senpai's screen: {desc}. Decide whether this supports his goal. If it clearly does, "
               "give at most a very short encouragement. If it looks like a distraction, nudge him gently and, "
               "if one open window is clearly the distraction, offer to close it using the [[CLOSE: ...]] tag. "
               "If there is nothing worth saying, reply exactly [[SKIP]]. "
               "Reply ONLY in {lang}, as Emmy, 1-2 short sentences.]")
CAM_HINT = ("[You see senpai through the webcam: {desc}. React to it in character as Emmy, warmly: "
            "1-2 short sentences. If nothing is worth saying, reply exactly [[SKIP]]. Reply ONLY in {lang}.]")
SCREEN_PROMPT = ("Describe in one or two short sentences what the user is doing on this computer screenshot "
                 "(which app, game, video, website or code). Do not read out private data such as emails, "
                 "passwords or personal messages. If it is just an empty desktop or nothing meaningful, "
                 "answer exactly: NOTHING")
CAM_PROMPT = ("Describe in one short sentence how the person in this webcam image looks "
              "(tired, smiling, focused...). If no person is visible or the image is dark, answer exactly: NOTHING")

LANGS = {
    "pl": dict(
        label="Polski", stt="pl-PL", espeak="pl", lang_name="Polish",
        voice="pl-PL-ZofiaNeural", pitch="+10Hz", rate="+5%", speed=1.0,
        fallback=dict(voice="pl_PL-gosia-medium", speed=1.12, length="0.95"),
        greet="Cześć senpai! Gotowa do rozmowy! ✨",
        system="Jesteś Emmy, słodką, wesołą dziewczynką z anime i rozmawiasz ze swoim senpai. "
               "ZAWSZE odpowiadaj po polsku, w 1-2 krótkich zdaniach, ciepło i zalotnie. "
               "Nie zachowuj się jak sztywny asystent i nie pytaj, w czym możesz pomóc. "
               "Reaguj na to, co powiedział senpai, i czasem dodaj emotikon (o^^o) lub (๑>◡<๑).",
        examples=[("Cześć", "Hejka, senpai! (๑>◡<๑) Tak się cieszę, że wpadłeś!"),
                  ("Nie chce mi się dziś pracować",
                   "Rozumiem, senpai... (o^^o) Zrób tylko jeden malutki krok do celu, a potem zobaczymy, dobrze?")],
        cb=("🎙️ Nasłuch", "💬 Zagaduje", "👁️ Widzi ekran"), goal_btn="📝 Edytuj cel",
        st=dict(idle="💤 Czekam, aż coś powiesz...", hear="🎙️ Słyszę Cię...", think="🧠 Myślę...",
                speak="🗣️ Mówię...", wait="👂 Czekam na Twoją odpowiedź...", off="🔇 Nasłuch wyłączony"),
        confirm_q="Czy mam zamknąć:", yes="✅ Tak", no="❌ Nie",
        closed="Gotowe, zamknięte! ✨", cancelled="Dobrze, zostawiam! (o^^o)",
        none_found="Nie widzę takiego okna, senpai.", too_many="Pasuje za dużo okien ({n}) - powiedz dokładniej.",
        yes_words=["tak", "jasne", "zamknij", "dawaj", "okej", "ok", "śmiało", "proszę", "pewnie",
                   "oczywiście", "no dobra", "dobrze", "zgoda"],
        no_words=["nie", "anuluj", "stop", "zostaw", "później", "nie teraz"],
        no_goal="(brak celu - edytuj cel.txt)",
        lang_set="Język rozmowy: polski",
    ),
    "en": dict(
        label="English", stt="en-US", espeak="en", lang_name="English",
        voice="en-US-AnaNeural", pitch="+3Hz", rate="+5%", speed=1.0,
        fallback=dict(voice="en_US-amy-medium", speed=1.08, length="0.95"),
        greet="Hi senpai! I'm ready to chat! ✨",
        system="You are Emmy, a sweet, cheerful anime girl chatting with your senpai. "
               "ALWAYS reply in English, in 1-2 short sentences, warm and a little flirty. "
               "Never act like a stiff assistant and never ask how you can help. "
               "React to what senpai says and sometimes add a kaomoji like (o^^o) or (๑>◡<๑).",
        examples=[("Hi", "Heeey, senpai! (๑>◡<๑) I'm so happy you're here!"),
                  ("I don't feel like working today",
                   "I get it, senpai... (o^^o) Just take one tiny step toward your goal, then we'll see, okay?")],
        cb=("🎙️ Listening", "💬 Starts chats", "👁️ Sees screen"), goal_btn="📝 Edit goal",
        st=dict(idle="💤 Waiting for you to speak...", hear="🎙️ I hear you...", think="🧠 Thinking...",
                speak="🗣️ Speaking...", wait="👂 Waiting for your answer...", off="🔇 Listening is off"),
        confirm_q="Should I close:", yes="✅ Yes", no="❌ No",
        closed="Done, closed! ✨", cancelled="Okay, I'll leave it! (o^^o)",
        none_found="I can't see that window, senpai.", too_many="Too many windows match ({n}) - be more specific.",
        yes_words=["yes", "yeah", "yep", "sure", "ok", "okay", "do it", "go ahead", "close it", "please", "fine"],
        no_words=["no", "nope", "don't", "dont", "cancel", "stop", "leave it", "not now"],
        no_goal="(no goal - edit cel.txt)",
        lang_set="Conversation language: English",
    ),
    "ja": dict(
        label="日本語", stt="ja-JP", espeak="ja", lang_name="Japanese",
        voice="ja-JP-NanamiNeural", pitch="+10Hz", rate="+5%", speed=1.0,
        fallback=None,   # Piper nie ma japońskiego głosu - awaryjnie espeak-ng
        greet="こんにちは、先輩！お話ししよう！✨",
        system="あなたはエミー、先輩とおしゃべりする甘くて明るいアニメの女の子です。"
               "必ず日本語で、1〜2文の短いかわいい口調で答えてください。"
               "堅いアシスタントのように振る舞わず、「何かお手伝いしましょうか」とは聞かないでください。"
               "先輩の話に反応して、時々 (o^^o) や (๑>◡<๑) の顔文字を使ってください。",
        examples=[("こんにちは", "先輩、来てくれたんだ！(๑>◡<๑) 嬉しいな！"),
                  ("今日は働きたくない",
                   "わかるよ、先輩… (o^^o) 目標に向かって、ほんの小さな一歩だけやってみよう？")],
        cb=("🎙️ 聞く", "💬 話しかける", "👁️ 画面を見る"), goal_btn="📝 目標を編集",
        st=dict(idle="💤 話しかけるのを待ってるよ…", hear="🎙️ 聞いてるよ…", think="🧠 考え中…",
                speak="🗣️ 話してるよ…", wait="👂 返事を待ってるよ…", off="🔇 マイクオフ"),
        confirm_q="閉じてもいい？", yes="✅ はい", no="❌ いいえ",
        closed="閉じたよ！✨", cancelled="わかった、そのままにするね！(o^^o)",
        none_found="そのウィンドウは見えないよ、先輩。", too_many="該当するウィンドウが多すぎるよ（{n}）。",
        yes_words=["はい", "うん", "お願い", "いいよ", "閉じて", "オッケー", "ok"],
        no_words=["いいえ", "だめ", "ダメ", "やめて", "いや", "やめ", "キャンセル"],
        no_goal="（目標なし - cel.txt を編集）",
        lang_set="会話の言語：日本語",
    ),
}

EMOTION_EXPRESSIONS = {}   # ręczne mapowanie emocji -> ekspresje (nazwa pliku bez ".exp3.json")

EXPRESSION_HINTS = {
    "happy": ["улыб", "радост", "смех", "счаст", "блик", "happy", "smile"],
    "love": ["сердц", "сердеч", "люб", "heart", "love"],
    "sad": ["груст", "плак", "слез", "слёз", "расстро", "sad", "cry"],
    "angry": ["зл", "сердит", "angry", "mad"],
    "surprised": ["удив", "шок", "пуст", "surpris", "shock"],
    "shy": ["смущ", "румян", "щек", "щёк", "blush", "shy"],
}

POSES = {
    "neutral": {},
    "listening": {"ParamAngleZ": 6, "ParamAngleY": 4},
    "waiting": {"ParamAngleZ": 5, "ParamAngleY": 3, "ParamEyeBallY": 0.3},
    "thinking": {"ParamAngleZ": 10, "ParamAngleY": 10, "ParamEyeBallX": 0.6, "ParamEyeBallY": 0.7,
                 "ParamMouthForm": -0.2},
    "happy": {"ParamMouthForm": 1.0, "ParamEyeLSmile": 0.8, "ParamEyeRSmile": 0.8, "ParamAngleZ": 5,
              "ParamCheek": 0.4},
    "love": {"ParamMouthForm": 1.0, "ParamEyeLSmile": 1.0, "ParamEyeRSmile": 1.0, "ParamCheek": 1.0,
             "ParamAngleZ": 8},
    "sad": {"ParamMouthForm": -1.0, "ParamAngleZ": -8, "ParamAngleY": -10, "ParamBrowLAngle": -0.6,
            "ParamBrowRAngle": -0.6},
    "angry": {"ParamMouthForm": -0.7, "ParamBrowLAngle": -1.0, "ParamBrowRAngle": -1.0,
              "ParamBrowLY": -0.8, "ParamBrowRY": -0.8, "ParamAngleY": -4},
    "surprised": {"ParamBrowLY": 1.0, "ParamBrowRY": 1.0, "ParamEyeBallY": 0.2, "ParamAngleY": 6},
    "shy": {"ParamCheek": 1.0, "ParamAngleY": -8, "ParamAngleZ": 10, "ParamEyeBallY": -0.5,
            "ParamMouthForm": 0.3},
}

EMOTION_KEYWORDS = {
    "love": ["kocham", "uwielbiam", "lubię", "lubie", "serduszk", "buziak", "i love", "love you", "adore",
             "大好き", "愛", "好き", "❤", "💕", "💖", "😍"],
    "happy": ["haha", "hihi", "super", "świetnie", "swietnie", "cieszę", "ciesze", "fajnie", "yay",
              "cześć", "czesc", "witaj", "dziękuję", "dziekuje", "hello", "great", "glad", "thank",
              "wonderful", "こんにちは", "嬉しい", "やった", "ありがとう", "楽しい", "わーい", "^^", "◡", "✨", "😊", "😄", "♪"],
    "sad": ["smutn", "przykro", "niestety", "szkoda", "przepraszam", "płaczę", "placze", "sorry", "sad",
            "unfortunately", "miss you", "悲しい", "ごめん", "寂しい", "残念", "😢", "😭", "🥺"],
    "angry": ["zły", "zla ", "wściek", "wsciek", "głupi", "glupi", "denerwuj", "baka", "angry", "annoying",
              "stupid", "怒", "ばか", "バカ", "むかつく", "😠", "😡"],
    "surprised": ["wow", "ojej", "niesamowit", "naprawdę?", "naprawde?", "!?", "really?", "oh my", "surpris",
                  "びっくり", "えっ", "うそ", "すごい", "😮", "😲"],
    "shy": ["wstyd", "rumie", "senpai", "nieśmia", "niesmia", "blush", "embarrass", "shy", "恥ずかしい",
            "照れ", "先輩", "😳"],
}

BG, BG_CHAT, FG, ACCENT, ACCENT_ACTIVE, TITLE_FG = (
    "#ffe6f0", "#fff0f5", "#4a4a4a", "#ff80bf", "#ff4da6", "#d63384")

ENV_STEP = 0.025
LIP_DELAY = 0.12


# ======================= POMOCNICZE =======================
def clamp(v, lo, hi):
    return max(lo, min(hi, v))


def detect_emotion(text, default="neutral"):
    t = text.lower()
    scores = {e: sum(t.count(k) for k in kws) for e, kws in EMOTION_KEYWORDS.items()}
    best = max(scores, key=scores.get)
    return best if scores[best] > 0 else default


def clean_for_tts(text):
    """Usuwa emotikony/kaomoji, żeby syntezator ich nie 'czytał'."""
    text = re.sub(r"\([^)]*[\^◡๑<>~;_ω・][^)]*\)", " ", text)
    text = "".join(ch for ch in text if ch.isalnum() or ch.isspace() or ch in ".,!?;:'\"-–…、。！？ー")
    return re.sub(r"\s+", " ", text).strip()


def similar(a, b, limit=0.55):
    ta, tb = set(re.findall(r"\w+", a.lower())), set(re.findall(r"\w+", b.lower()))
    if not ta or not tb:
        return False
    return len(ta & tb) / len(ta | tb) >= limit


# ---------- cel ----------
_goal_cache = {"mtime": None, "text": ""}


def read_goal():
    """Czyta cel z pliku (z cache po czasie modyfikacji); pomija pola z niewypełnionymi nawiasami."""
    try:
        if not GOAL_FILE.exists():
            GOAL_FILE.write_text(GOAL_TEMPLATE, encoding="utf-8")
        m = GOAL_FILE.stat().st_mtime
        if m != _goal_cache["mtime"]:
            keep = []
            for line in GOAL_FILE.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if not line:
                    continue
                _, sep, val = line.partition(":")
                if sep and (not val.strip() or val.strip().startswith("(")):
                    continue
                keep.append(line)
            _goal_cache.update(mtime=m, text="\n".join(keep)[:GOAL_MAX_CHARS])
        return _goal_cache["text"]
    except Exception as e:
        print(f"Błąd odczytu celu: {e}")
        return ""


def goal_main(goal):
    """Zwraca główny cel (linia CEL: ...) albo pierwszą wolną linię; pusty string, gdy brak celu."""
    for line in goal.splitlines():
        k, sep, v = line.partition(":")
        if sep and k.strip().upper() in GOAL_KEYS:
            return v.strip()
    for line in goal.splitlines():
        k, sep, _ = line.partition(":")
        if not (sep and k.strip().upper() in KNOWN_KEYS):
            return line.strip()
    return ""


# ---------- okna (wmctrl; X11/XWayland) ----------
def list_windows():
    if not WINDOW_TOOLS or not shutil.which("wmctrl"):
        return []
    try:
        out = subprocess.run(["wmctrl", "-l"], capture_output=True, text=True, timeout=3).stdout
    except Exception:
        return []
    wins = []
    for line in out.splitlines():
        parts = line.split(None, 3)
        if len(parts) < 4 or parts[1] == "-1":    # -1 = okna przyklejone (panele, pulpit)
            continue
        wins.append((parts[0], parts[3].strip()))
    return wins


def is_protected(title):
    low = title.lower()
    return any(p in low for p in PROTECTED_WINDOWS)


def find_windows(fragment):
    frag = fragment.lower().strip()
    if len(frag) < 2:
        return []
    return [(w, t) for w, t in list_windows() if frag in t.lower() and not is_protected(t)]


def close_windows(wins):
    """Grzeczne zamknięcie (jak kliknięcie X) - programy same zapytają o zapis zmian."""
    alive = {w for w, _ in list_windows()}
    n = 0
    for wid, title in wins:
        if wid in alive and not is_protected(title):
            try:
                subprocess.run(["wmctrl", "-i", "-c", wid], timeout=3)
                n += 1
                print(f"[okno] zamykam: {title}")
            except Exception as e:
                print(f"Nie udało się zamknąć okna: {e}")
    return n


# ---------- odpowiedzi modelu ----------
CLOSE_RE = re.compile(r"\[+\s*CLOSE\s*:\s*(.*?)\s*\]+", re.I | re.S)
SKIP_RE = re.compile(r"\[+\s*SKIP\s*\]+", re.I)


def parse_reply(raw):
    """Zwraca (tekst do wyświetlenia/powiedzenia, cel zamknięcia lub None, czy pominąć)."""
    skip = bool(SKIP_RE.search(raw))
    m = CLOSE_RE.search(raw)
    target = m.group(1).strip() if m else None
    text = SKIP_RE.sub("", CLOSE_RE.sub("", raw)).strip()
    return text, target, skip


def classify_yes_no(text, cfg):
    """True = tak, False = nie, None = to nie jest odpowiedź na pytanie o potwierdzenie."""
    t = text.lower().strip()
    if len(t.split()) > 6 or len(t) > 24:
        return None

    def has(words):
        for w in words:
            if re.search(r"[\u3040-\u30ff\u4e00-\u9fff]", w):
                if w in t:
                    return True
            elif re.search(r"(?<!\w)" + re.escape(w) + r"(?!\w)", t):
                return True
        return False

    if has(cfg["no_words"]):
        return False
    if has(cfg["yes_words"]):
        return True
    return None


def screenshot_cli():
    """Zrzut ekranu zewnętrznym narzędziem (przydatne na Wayland, gdzie mss widzi czerń)."""
    f = tempfile.NamedTemporaryFile(delete=False, suffix=".png")
    f.close()
    path = f.name
    try:
        for cmd in (["spectacle", "-b", "-n", "-f", "-o", path], ["grim", path], ["gnome-screenshot", "-f", path]):
            if not shutil.which(cmd[0]):
                continue
            try:
                subprocess.run(cmd, capture_output=True, timeout=20)
                if os.path.exists(path) and os.path.getsize(path) > 1000:
                    return Image.open(path).convert("RGB")
            except Exception as e:
                print(f"[ekran] {cmd[0]} nie zadziałał: {e}")
        return None
    finally:
        if os.path.exists(path):
            os.remove(path)


class Lip:
    env = []
    start = 0.0
    active = False
    speed = 1.0

    @classmethod
    def level(cls, now):
        if not cls.active or now < cls.start:
            return 0.0
        if not cls.env:  # brak obwiedni (np. bez ffmpeg) - prosta animacja
            return abs(math.sin(now * 11)) * 0.8
        i = int((now - cls.start) * cls.speed / ENV_STEP)
        if 0 <= i < len(cls.env):
            v = cls.env[i]
            return 0.0 if v < 0.12 else float(v)
        return 0.0


def compute_envelope(path):
    with wave.open(path) as wf:
        rate, ch = wf.getframerate(), wf.getnchannels()
        data = np.frombuffer(wf.readframes(wf.getnframes()), dtype=np.int16).astype(np.float32)
    if ch > 1:
        data = data.reshape(-1, ch).mean(axis=1)
    step = int(rate * ENV_STEP)
    frames = len(data) // step
    if frames == 0:
        return []
    rms = np.sqrt((data[:frames * step].reshape(frames, step) ** 2).mean(axis=1))
    ref = float(np.percentile(rms, 90)) or 1.0
    return np.clip(rms / ref, 0, 1).tolist()


# ======================= GŁOSY =======================
def voice_paths(name):
    return VOICE_DIR / f"{name}.onnx", VOICE_DIR / f"{name}.onnx.json"


def ensure_piper_voice(name):
    with _voice_lock:
        VOICE_DIR.mkdir(parents=True, exist_ok=True)
        onnx, js = voice_paths(name)
        lang_region, speaker, quality = name.split("-")
        lang = lang_region.split("_")[0]
        base = f"https://huggingface.co/rhasspy/piper-voices/resolve/main/{lang}/{lang_region}/{speaker}/{quality}/"
        try:
            for path in (onnx, js):
                if not path.exists():
                    print(f"Pobieram głos Piper: {path.name}")
                    tmp = path.with_suffix(path.suffix + ".part")
                    urllib.request.urlretrieve(base + path.name, tmp)
                    tmp.rename(path)
            return True
        except Exception as e:
            print(f"Błąd pobierania głosu Piper ({name}): {e}")
            return False


def synth_piper(text, fb, out_wav):
    if not ensure_piper_voice(fb["voice"]):
        return False
    onnx, _ = voice_paths(fb["voice"])
    ls = fb.get("length", "1.0")
    attempts = [
        ["--output_file", out_wav, "--length_scale", ls],
        ["--output_file", out_wav],
        ["-f", out_wav, "--length-scale", ls],
        ["-f", out_wav],
    ]
    last = None
    for extra in attempts:
        last = subprocess.run(["piper", "--model", str(onnx), *extra], input=text.encode("utf-8"),
                              capture_output=True, timeout=90)
        if last.returncode == 0 and os.path.exists(out_wav) and os.path.getsize(out_wav) > 1000:
            return True
    if last is not None:
        print("Piper nie zadziałał:", last.stderr.decode(errors="ignore")[-400:])
    return False


def synth_edge(text, cfg, out_mp3):
    cmd = [sys.executable, "-m", "edge_tts", "--voice", cfg["voice"],
           f"--pitch={cfg['pitch']}", f"--rate={cfg['rate']}", f"--text={text}", "--write-media", out_mp3]
    try:
        p = subprocess.run(cmd, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        print("edge-tts: przekroczono czas (brak internetu?)")
        return False
    if p.returncode == 0 and os.path.exists(out_mp3) and os.path.getsize(out_mp3) > 1000:
        return True
    print("edge-tts nie zadziałał:", p.stderr.decode(errors="ignore")[-300:])
    return False


def speak(text, lang, on_start=None, on_end=None):
    def run():
        cfg = LANGS[lang]
        temps = []

        def tmpfile(suffix):
            f = tempfile.NamedTemporaryFile(delete=False, suffix=suffix)
            f.close()
            temps.append(f.name)
            return f.name

        try:
            clean = clean_for_tts(text)
            if not clean:
                return
            play_file, wav_file, speed = None, None, 1.0

            if EDGE_OK:
                mp3 = tmpfile(".mp3")
                if synth_edge(clean, cfg, mp3):
                    play_file, speed = mp3, cfg.get("speed", 1.0)
                    if shutil.which("ffmpeg"):
                        wav = tmpfile(".wav")
                        subprocess.run(["ffmpeg", "-y", "-loglevel", "quiet", "-i", mp3, "-ar", "24000",
                                        "-ac", "1", wav], timeout=60)
                        if os.path.getsize(wav) > 1000:
                            wav_file = wav
                    else:
                        print("Brak ffmpeg - usta poruszają się wg prostej animacji (zainstaluj ffmpeg).")

            fb = cfg.get("fallback")
            if not play_file and fb:
                wav = tmpfile(".wav")
                if synth_piper(clean, fb, wav):
                    play_file = wav_file = wav
                    speed = fb.get("speed", 1.0)

            if not play_file and shutil.which("espeak-ng"):
                wav = tmpfile(".wav")
                subprocess.run(["espeak-ng", "-v", cfg["espeak"], "-p", "75", "-w", wav, clean], timeout=30)
                if os.path.getsize(wav) > 1000:
                    play_file = wav_file = wav
                    speed = 1.0

            if not play_file:
                print("Nie udało się wygenerować mowy.")
                return

            try:
                Lip.env = compute_envelope(wav_file) if wav_file else []
            except Exception:
                Lip.env = []
            Lip.speed = speed
            Lip.start = time.time() + LIP_DELAY
            Lip.active = True
            if on_start:
                on_start((len(Lip.env) * ENV_STEP if Lip.env else 4.0) / speed)

            subprocess.run(["mpv", "--no-video", "--really-quiet", f"--speed={speed}",
                            "--audio-pitch-correction=no", play_file],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except FileNotFoundError as e:
            print(f"Brak programu (piper/mpv): {e}")
        except Exception as e:
            print(f"Błąd syntezatora: {e}")
        finally:
            Lip.active = False
            for t in temps:
                if os.path.exists(t):
                    os.remove(t)
            if on_end:
                on_end()

    threading.Thread(target=run, daemon=True).start()


def ensure_ollama_running():
    try:
        urllib.request.urlopen("http://localhost:11434/api/tags", timeout=1)
        return True
    except Exception:
        try:
            subprocess.Popen(["ollama", "serve"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            time.sleep(3)
            return True
        except Exception:
            return False


def find_mic():
    try:
        devices = sd.query_devices()
        for i, d in enumerate(devices):
            if d["max_input_channels"] > 0 and "creative" in d["name"].lower():
                return i, min(2, d["max_input_channels"])
        default_in = sd.default.device[0]
        if default_in is not None and default_in >= 0:
            return default_in, max(1, min(2, devices[default_in]["max_input_channels"]))
    except Exception as e:
        print(f"Błąd wyszukiwania mikrofonu: {e}")
    return None, 1


# ======================= GUI =======================
class AnimeAIGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Lokalna Anime Waifu AI (Live2D + TTS + Qwen) 🌸")
        self.root.geometry("460x720")
        self.root.config(bg=BG)

        # ---------- stan (WSZYSTKO przed uruchomieniem wątków) ----------
        self.running = True
        self.ui_queue = queue.Queue()
        self.lang = DEFAULT_LANG
        self.started = time.time()
        self.turn_lock = threading.Lock()
        self.processing = False
        self.user_speaking = False
        self.mute_until = 0.0
        self.last_activity = time.time()
        self.proactive_due = 0.0
        self.unanswered = 0
        self.awaiting_until = 0.0
        self.last_screen_desc = ""
        self.last_stt_error = 0.0
        self.listen_on = True
        self.talk_on = True
        self.screen_on = SCREEN_AVAILABLE
        self._status_txt = ""
        self._goal_check = 0.0
        self._vision_warned = False
        self._screen_warned = False

        # potwierdzanie zamknięcia okna
        self.pending = None
        self.pending_lock = threading.Lock()
        self.confirm_dlg = None

        # postać
        self.model = None
        self.win = None
        self.live2d_running = False
        self.transparent = TRANSPARENT
        self.state = "idle"            # idle / listening / thinking / speaking
        self.emotion = "neutral"
        self.emotion_until = 0.0
        self.pose = {}
        self.scale = 1.0
        self.last_t = time.time()
        self.dragging = False
        self.drag_moved = False
        self.drag_start_ptr = (0, 0)
        self.drag_start_pos = (0, 0)
        self.chat_visible = True
        self.param_ids = set()
        self.expr_ids = {}
        self.param_error_shown = False

        self.messages = []
        self.head_len = 0
        self.reset_conversation()
        self.note_activity()

        # ---------- UI ----------
        tk.Label(root, text="(๑>◡<๑)\n🌸 Chibi Emmy Gotowa! 🌸",
                 font=("Arial", 14, "bold"), bg=BG, fg=TITLE_FG).pack(pady=(12, 6))

        lang_frame = tk.Frame(root, bg=BG)
        lang_frame.pack(pady=(0, 4))
        self.lang_var = tk.StringVar(value=self.lang)
        for code, cfg in LANGS.items():
            tk.Radiobutton(lang_frame, text=cfg["label"], value=code, variable=self.lang_var,
                           command=self.on_lang_change, font=("Arial", 11, "bold"), bg=BG, fg=TITLE_FG,
                           activebackground=BG, activeforeground=ACCENT_ACTIVE,
                           selectcolor="#ffd0e6").pack(side=tk.LEFT, padx=8)

        self.goal_var = tk.StringVar()
        tk.Label(root, textvariable=self.goal_var, font=("Arial", 10, "bold"), bg=BG, fg=TITLE_FG,
                 wraplength=420, justify="center").pack(pady=(2, 2))

        self.status_var = tk.StringVar()
        tk.Label(root, textvariable=self.status_var, font=("Arial", 11, "bold"),
                 bg=BG, fg=TITLE_FG).pack(pady=(4, 2))
        self.level_bar = ttk.Progressbar(root, length=300, maximum=100)
        self.level_bar.pack(pady=(0, 4))

        self.chat_log = scrolledtext.ScrolledText(root, wrap=tk.WORD, width=52, height=18,
                                                  font=("Arial", 10), bg=BG_CHAT, fg=FG)
        self.chat_log.pack(pady=5)
        self.chat_log.config(state=tk.DISABLED)

        toggles = tk.Frame(root, bg=BG)
        toggles.pack(pady=(8, 4))
        self.listen_var = tk.BooleanVar(value=self.listen_on)
        self.talk_var = tk.BooleanVar(value=self.talk_on)
        self.screen_var = tk.BooleanVar(value=self.screen_on)
        self.toggle_widgets = []
        for var in (self.listen_var, self.talk_var, self.screen_var):
            cb = tk.Checkbutton(toggles, variable=var, command=self.on_toggle, font=("Arial", 11, "bold"),
                                bg=BG, fg=TITLE_FG, activebackground=BG, selectcolor="#ffd0e6")
            cb.pack(side=tk.LEFT, padx=8)
            self.toggle_widgets.append(cb)

        self.goal_btn = tk.Button(root, command=self.open_goal_file, font=("Arial", 11, "bold"),
                                  bg=ACCENT, fg="white", activebackground=ACCENT_ACTIVE, padx=10, pady=3)
        self.goal_btn.pack(pady=6)
        self.apply_ui_language()

        self.append_chat("Waifu", LANGS[self.lang]["greet"])

        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.process_queue()

        # ---------- wątki w tle ----------
        threading.Thread(target=self.startup_checks, daemon=True).start()
        threading.Thread(target=self.prepare_voice, daemon=True).start()
        threading.Thread(target=self.vad_loop, daemon=True).start()
        threading.Thread(target=self.proactive_loop, daemon=True).start()
        threading.Thread(target=self.screen_loop, daemon=True).start()

        if LIVE2D_AVAILABLE:
            self.root.after(300, self.init_live2d_window)
        else:
            self.append_chat("System", "Live2D niedostępny - sprawdź konsolę.")

    # ---------- UI pomocnicze ----------
    def apply_ui_language(self):
        cfg = LANGS[self.lang]
        for widget, text in zip(self.toggle_widgets, cfg["cb"]):
            widget.config(text=text)
        self.goal_btn.config(text=cfg["goal_btn"])
        self._status_txt = ""
        self._goal_check = 0.0

    def open_goal_file(self):
        read_goal()   # utworzy plik z szablonem, jeśli go nie ma
        try:
            subprocess.Popen(["xdg-open", str(GOAL_FILE)], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        except FileNotFoundError:
            self.append_chat("System", f"Otwórz ręcznie plik: {GOAL_FILE}")

    def on_toggle(self):
        self.listen_on = self.listen_var.get()
        self.talk_on = self.talk_var.get()
        self.screen_on = self.screen_var.get() and SCREEN_AVAILABLE
        if self.screen_var.get() and not SCREEN_AVAILABLE:
            self.append_chat("System", "Brak bibliotek: pip install mss pillow")
        if self.listen_on:
            self.note_activity()

    def refresh_status(self):
        st = LANGS[self.lang]["st"]
        if self.state == "listening":
            key = "hear"
        elif self.state == "thinking":
            key = "think"
        elif self.state == "speaking":
            key = "speak"
        elif not self.listen_on:
            key = "off"
        elif self.pending_active() or time.time() < self.awaiting_until:
            key = "wait"
        else:
            key = "idle"
        if st[key] != self._status_txt:
            self._status_txt = st[key]
            self.status_var.set(st[key])

        now = time.time()
        if now - self._goal_check > 2.0:
            self._goal_check = now
            main = goal_main(read_goal())
            self.goal_var.set("🎯 " + (main[:90] if main else LANGS[self.lang]["no_goal"]))

    def process_queue(self):
        try:
            while True:
                kind, payload = self.ui_queue.get_nowait()
                if kind == "chat":
                    sender, message = payload
                    self.chat_log.config(state=tk.NORMAL)
                    self.chat_log.insert(tk.END, f"{sender}: {message}\n")
                    self.chat_log.config(state=tk.DISABLED)
                    self.chat_log.see(tk.END)
                elif kind == "state":
                    self.state = payload
                elif kind == "emotion":
                    self.apply_emotion(*payload)
                elif kind == "extend":
                    self.emotion_until = max(self.emotion_until, time.time() + payload)
                elif kind == "level":
                    rms, thr = payload
                    self.level_bar["value"] = clamp(rms / thr * 50, 0, 100)
                elif kind == "confirm":
                    self.show_confirm(payload)
                elif kind == "confirm_close":
                    self.close_confirm_dialog()
        except queue.Empty:
            pass
        self.refresh_status()
        self.root.after(50, self.process_queue)

    def append_chat(self, sender, message):
        self.ui_queue.put(("chat", (sender, message)))

    def post(self, kind, payload=None):
        self.ui_queue.put((kind, payload))

    # ---------- potwierdzanie zamknięcia okna ----------
    def pending_active(self):
        p = self.pending
        return bool(p and time.time() < p["until"])

    def stage_close(self, target):
        cfg = LANGS[self.lang]
        wins = find_windows(target)
        if not wins:
            self.append_chat("System", cfg["none_found"])
            return
        if len(wins) > 3:
            self.append_chat("System", cfg["too_many"].format(n=len(wins)))
            return
        with self.pending_lock:
            self.pending = {"wins": wins, "until": time.time() + CONFIRM_TIMEOUT}
        self.post("confirm", [t for _, t in wins])

    def show_confirm(self, titles):
        self.close_confirm_dialog()
        cfg = LANGS[self.lang]
        dlg = tk.Toplevel(self.root)
        dlg.title("Emmy 🌸")
        dlg.config(bg=BG)
        try:
            dlg.attributes("-topmost", True)
        except Exception:
            pass
        text = cfg["confirm_q"] + "\n\n" + "\n".join("• " + t[:70] for t in titles)
        tk.Label(dlg, text=text, font=("Arial", 11, "bold"), bg=BG, fg=TITLE_FG,
                 justify="left").pack(padx=18, pady=14)
        row = tk.Frame(dlg, bg=BG)
        row.pack(pady=(0, 14))
        for label, answer in ((cfg["yes"], True), (cfg["no"], False)):
            tk.Button(row, text=label, command=lambda a=answer: self.resolve_pending(a),
                      font=("Arial", 11, "bold"), bg=ACCENT, fg="white", activebackground=ACCENT_ACTIVE,
                      padx=12).pack(side=tk.LEFT, padx=8)
        dlg.protocol("WM_DELETE_WINDOW", lambda: self.resolve_pending(False))
        self.confirm_dlg = dlg
        self.root.after(int(CONFIRM_TIMEOUT * 1000) + 500, self.expire_pending)

    def close_confirm_dialog(self):
        if self.confirm_dlg is not None:
            try:
                self.confirm_dlg.destroy()
            except Exception:
                pass
            self.confirm_dlg = None

    def expire_pending(self):
        expired = False
        with self.pending_lock:
            if self.pending and time.time() >= self.pending["until"]:
                self.pending = None
                expired = True
        if expired:
            self.close_confirm_dialog()

    def resolve_pending(self, yes):
        with self.pending_lock:
            p, self.pending = self.pending, None
        self.post("confirm_close")
        if not p:
            return False
        cfg = LANGS[self.lang]
        if yes:
            close_windows(p["wins"])
            msg, emo = cfg["closed"], "happy"
        else:
            msg, emo = cfg["cancelled"], "neutral"
        threading.Thread(target=self.run_turn, kwargs=dict(canned=msg, emotion=emo, kind="user"),
                         daemon=True).start()
        return True

    # ---------- język / rozmowa ----------
    def initial_messages(self, lang):
        msgs = []
        for u, a in LANGS[lang].get("examples", []):
            msgs += [{"role": "user", "content": u}, {"role": "assistant", "content": a}]
        return msgs

    def reset_conversation(self):
        self.messages = self.initial_messages(self.lang)
        self.head_len = len(self.messages)

    def build_system(self):
        """Prompt systemowy budowany na bieżąco: persona + zasady + cel + godzina + otwarte okna."""
        cfg = LANGS[self.lang]
        minutes = int((time.time() - self.started) / 60)
        parts = [cfg["system"], COACH_RULES,
                 f"Local time: {time.strftime('%H:%M')}. You have been chatting with senpai for {minutes} min."]
        goal = read_goal()
        if goal_main(goal):
            parts.append("Senpai's goal file (his own words):\n" + goal)
        else:
            parts.append("Senpai has not written a goal yet. Sometimes, gently, ask what he wants to achieve "
                         "today and suggest he writes it using the 'Edit goal' button.")
        wins = [t for _, t in list_windows() if not is_protected(t)]
        if wins:
            parts.append("Open windows (titles):\n" + "\n".join("- " + t[:80] for t in wins[:15]))
        else:
            parts.append("(You cannot see any open windows right now, so you cannot close anything.)")
        return "\n\n".join(parts)

    def prepare_voice(self):
        fb = LANGS[self.lang].get("fallback")
        if not EDGE_OK and fb:
            ensure_piper_voice(fb["voice"])

    def on_lang_change(self):
        self.lang = self.lang_var.get()
        self.reset_conversation()
        self.apply_ui_language()
        self.append_chat("System", LANGS[self.lang]["lang_set"])
        self.append_chat("Waifu", LANGS[self.lang]["greet"])
        self.note_activity()
        threading.Thread(target=self.prepare_voice, daemon=True).start()

    def startup_checks(self):
        ensure_ollama_running()
        self.check_ollama()
        if USE_EDGE and not EDGE_OK:
            self.append_chat("System", "ℹ️ Brak edge-tts, więc używam lokalnego głosu. "
                                       "Ładniejszy głos: pip install edge-tts")
        if WINDOW_TOOLS and not shutil.which("wmctrl"):
            self.append_chat("System", "ℹ️ Żeby mogła widzieć i zamykać okna, zainstaluj wmctrl "
                                       "(np. sudo apt install wmctrl).")
        if os.environ.get("XDG_SESSION_TYPE", "").lower() == "wayland":
            self.append_chat("System", "ℹ️ Sesja Wayland: widzę tylko okna XWayland, a zrzuty ekranu mogą być "
                                       "czarne. Sesja X11 działa najlepiej.")

    def check_ollama(self):
        names = None
        for _ in range(10):
            try:
                with urllib.request.urlopen("http://localhost:11434/api/tags", timeout=2) as r:
                    names = [m["name"] for m in json.loads(r.read())["models"]]
                break
            except Exception:
                time.sleep(1)

        def has(model):
            return names is not None and (model in names or f"{model}:latest" in names)

        if names is None:
            self.append_chat("System", "⚠️ Ollama nie odpowiada. Uruchom: ollama serve")
            return
        if not has(OLLAMA_MODEL):
            self.append_chat("System", f"⚠️ Brak modelu {OLLAMA_MODEL}. Uruchom: ollama pull {OLLAMA_MODEL}")
        else:
            self.append_chat("System", f"Ollama OK, model: {OLLAMA_MODEL}")
        if self.screen_on and not has(VISION_MODEL):
            self._vision_warned = True
            self.append_chat("System", f"⚠️ Brak modelu wizyjnego (ekran). Uruchom: "
                                       f"ollama pull {VISION_MODEL.split(':')[0]}")

    # ---------- aktywność / tury rozmowy ----------
    def note_activity(self):
        now = time.time()
        self.last_activity = now
        factor = 2 ** min(self.unanswered, 3)
        self.proactive_due = now + random.uniform(IDLE_MIN, IDLE_MAX) * factor

    def generate_response(self, user_text=None, hint=None):
        """Zwraca surową odpowiedź modelu (może zawierać tagi) albo None."""
        try:
            if user_text is not None:
                self.messages.append({"role": "user", "content": user_text})
            if len(self.messages) > self.head_len + 12:
                self.messages = self.messages[:self.head_len] + self.messages[self.head_len:][-12:]
            send = [{"role": "system", "content": self.build_system()}] + list(self.messages)
            if hint:
                send.append({"role": "user", "content": hint})   # ukryta instrukcja - nie trafia do historii
            payload = {"model": OLLAMA_MODEL, "messages": send, "stream": False,
                       "options": OLLAMA_OPTIONS, "keep_alive": "30m"}
            req = urllib.request.Request(
                "http://localhost:11434/api/chat",
                data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json"},
            )
            with urllib.request.urlopen(req, timeout=120) as response:
                reply = json.loads(response.read().decode("utf-8"))["message"]["content"].strip()
            if not reply:
                raise ValueError("pusta odpowiedź")
            return reply
        except Exception as e:
            if user_text is not None and self.messages and self.messages[-1].get("content") == user_text:
                self.messages.pop()
            self.append_chat("System", f"⚠️ Ollama: {e}")
            return None

    def run_turn(self, user_text=None, hint=None, label="Waifu", kind="user", canned=None, emotion=None):
        """Jedna tura: odpowiedź AI (lub gotowy tekst) + głos. kind: user / idle / screen."""
        if kind == "user":
            got = self.turn_lock.acquire(timeout=60)
        else:
            got = self.turn_lock.acquire(blocking=False)   # samoistne wypowiedzi nie przerywają rozmowy
        if not got:
            return False
        lang = self.lang
        spoke = False
        try:
            self.post("state", "thinking")
            target = None
            if canned is not None:
                reply = canned
            else:
                raw = self.generate_response(user_text, hint)
                if not raw:
                    return False
                reply, target, skip = parse_reply(raw)
                if skip or not reply:
                    if user_text is not None and self.messages and self.messages[-1].get("content") == user_text:
                        self.messages.pop()
                    return False
                self.messages.append({"role": "assistant", "content": reply})

            self.append_chat(label, reply)
            emo = emotion or detect_emotion(reply)
            if emo == "neutral" and emotion is None:
                emo = detect_emotion(user_text or "", default="happy")
            self.post("state", "speaking")
            self.post("emotion", (emo, 8.0))
            done = threading.Event()
            speak(reply, lang, on_start=lambda d: self.post("extend", d + 2.0), on_end=done.set)
            done.wait(timeout=120)
            spoke = True
            if target:
                self.stage_close(target)   # okno z potwierdzeniem pojawia się po tym, jak skończy mówić
            return True
        finally:
            self.post("state", "idle")
            self.mute_until = time.time() + MUTE_AFTER_SPEECH
            if kind == "idle" and spoke:
                self.unanswered += 1
                self.awaiting_until = time.time() + REPLY_WAIT
            self.note_activity()
            self.turn_lock.release()

    def handle_utterance(self, audio16):
        cfg = LANGS[self.lang]
        try:
            self.post("state", "thinking")
            try:
                r = sr.Recognizer()
                data = sr.AudioData(audio16.tobytes(), SAMPLE_RATE, 2)
                text = r.recognize_google(data, language=cfg["stt"]).strip()
            except sr.UnknownValueError:
                self.post("state", "idle")
                return
            except Exception as e:
                print(f"Błąd rozpoznawania mowy: {e}")
                if time.time() - self.last_stt_error > 30:
                    self.last_stt_error = time.time()
                    self.append_chat("System", f"⚠️ Rozpoznawanie mowy (internet?): {e}")
                self.post("state", "idle")
                return
            if len(text) < 2:
                self.post("state", "idle")
                return
            self.unanswered = 0
            self.awaiting_until = 0.0
            self.append_chat("Ty", text)

            if self.pending_active():                      # odpowiedź na pytanie o zamknięcie okna
                ans = classify_yes_no(text, cfg)
                if ans is not None:
                    self.resolve_pending(ans)
                    return

            self.run_turn(user_text=text, kind="user")
        finally:
            self.processing = False

    # ---------- nasłuch (VAD) ----------
    def vad_loop(self):
        while self.running:
            if not self.listen_on:
                self.user_speaking = False
                time.sleep(0.3)
                continue
            try:
                self.run_vad_stream()
            except Exception as e:
                print(f"Błąd mikrofonu: {e}")
                self.append_chat("System", f"⚠️ Mikrofon: {e}")
                time.sleep(5)

    def run_vad_stream(self):
        mic_index, channels = find_mic()
        blocks = queue.Queue(maxsize=300)

        def cb(indata, frames, t, status):
            try:
                blocks.put_nowait(indata.astype(np.float32).mean(axis=1).astype(np.int16))
            except queue.Full:
                pass

        pre = collections.deque(maxlen=PRE_ROLL_BLOCKS)
        speech, rms_hist, calib = [], [], []
        in_speech, voiced, silence, voice_blocks, n = False, 0, 0, 0, 0
        noise = None

        with sd.InputStream(samplerate=SAMPLE_RATE, channels=channels, dtype="int16",
                            device=mic_index, blocksize=BLOCK, callback=cb):
            while self.running and self.listen_on:
                try:
                    blk = blocks.get(timeout=0.5)
                except queue.Empty:
                    continue
                rms = float(np.sqrt(np.mean(blk.astype(np.float32) ** 2)))
                now = time.time()

                if noise is None:                      # kalibracja szumu (ok. 1,3 s)
                    calib.append(rms)
                    if len(calib) >= 40:
                        noise = max(float(np.median(calib)), 5.0)
                        print(f"[mikrofon] szum={noise:.0f}, próg={max(MIN_THRESHOLD, noise * NOISE_FACTOR):.0f}")
                    continue

                thr = max(MIN_THRESHOLD, noise * NOISE_FACTOR)
                n += 1
                if n % 3 == 0:
                    self.post("level", (rms, thr))

                muted = self.turn_lock.locked() or self.processing or now < self.mute_until
                if muted:
                    in_speech, voiced, silence, voice_blocks = False, 0, 0, 0
                    self.user_speaking = False
                    speech = []
                    pre.clear()
                    continue

                is_voice = rms > thr
                if not in_speech:
                    pre.append(blk)
                    if is_voice:
                        voiced += 1
                    else:
                        voiced = 0
                        noise = 0.97 * noise + 0.03 * rms        # szum tła powoli się dostraja
                    if voiced >= START_BLOCKS:
                        in_speech, silence, voice_blocks = True, 0, voiced
                        self.user_speaking = True
                        speech, rms_hist = list(pre), []
                        self.post("state", "listening")
                        self.note_activity()
                else:
                    speech.append(blk)
                    rms_hist.append(rms)
                    if is_voice:
                        silence = 0
                        voice_blocks += 1
                    else:
                        silence += 1
                    too_long = len(speech) * BLOCK_S >= MAX_UTTERANCE
                    if silence * BLOCK_S >= END_SILENCE or too_long:
                        audio = np.concatenate(speech)
                        enough = voice_blocks * BLOCK_S >= MIN_SPEECH
                        in_speech, voiced, silence, voice_blocks = False, 0, 0, 0
                        self.user_speaking = False
                        speech = []
                        pre.clear()
                        if too_long and len(rms_hist) > 10:
                            p10, p90 = np.percentile(rms_hist, [10, 90])
                            if p90 / max(p10, 1.0) < 2.5:   # płaski dźwięk = hałas, nie mowa
                                noise = float(np.median(rms_hist))
                                print(f"[mikrofon] stały hałas - nowy szum={noise:.0f}")
                                enough = False
                        if enough:
                            self.processing = True
                            threading.Thread(target=self.handle_utterance, args=(audio,), daemon=True).start()
                        else:
                            self.post("state", "idle")

    # ---------- samoistne zagadywanie ----------
    def proactive_loop(self):
        while self.running:
            time.sleep(1.0)
            now = time.time()
            if not (self.talk_on and self.listen_on):
                continue
            if now < self.proactive_due or now < self.mute_until:
                continue
            if self.turn_lock.locked() or self.processing or self.user_speaking or self.pending_active():
                continue
            has_goal = bool(goal_main(read_goal()))
            pool = IDLE_TOPICS_GOAL if has_goal and random.random() < 0.7 else IDLE_TOPICS
            hint = IDLE_HINT.format(topic=random.choice(pool), lang=LANGS[self.lang]["lang_name"])
            self.run_turn(hint=hint, kind="idle")
            self.note_activity()   # gdy tura się nie udała - nie próbuj od razu ponownie

    # ---------- ekran / kamerka ----------
    def capture_screen(self):
        img = None
        try:
            with MSS() as sct:
                shot = sct.grab(sct.monitors[1])
                img = Image.frombytes("RGB", shot.size, shot.bgra, "raw", "BGRX")
        except Exception as e:
            print(f"[ekran] mss nie zadziałał: {e}")
        if img is not None and float(np.asarray(img.resize((64, 64))).mean()) >= 2:
            return img
        img = screenshot_cli()      # zapas dla Wayland: spectacle / grim / gnome-screenshot
        if img is not None:
            return img
        if not self._screen_warned:
            self._screen_warned = True
            self.append_chat("System", "⚠️ Nie mogę zrobić zrzutu ekranu (czarny obraz - Wayland?). "
                                       "Zaloguj się do sesji X11 albo zainstaluj spectacle/grim/gnome-screenshot.")
        return None

    def capture_webcam(self):
        cap = cv2.VideoCapture(WEBCAM_INDEX)
        ok, frame = cap.read()
        cap.release()
        if not ok:
            return None
        return Image.fromarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))

    def encode_image_to_base64(self, pil_image):
        img = pil_image.copy()
        img.thumbnail((768, 768), Image.Resampling.LANCZOS)
        buf = io.BytesIO()
        img.save(buf, format="JPEG", quality=85)
        return base64.b64encode(buf.getvalue()).decode("utf-8")

    def analyze_image(self, image_b64, prompt):
        try:
            payload = {
                "model": VISION_MODEL,
                "messages": [{"role": "user", "content": prompt, "images": [image_b64]}],
                "stream": False,
                "keep_alive": "5m",
                "options": {"temperature": 0.3, "num_predict": 100},
            }
            req = urllib.request.Request(
                "http://localhost:11434/api/chat",
                data=json.dumps(payload).encode("utf-8"),
                headers={"Content-Type": "application/json"},
            )
            with urllib.request.urlopen(req, timeout=180) as response:
                return json.loads(response.read().decode("utf-8"))["message"]["content"].strip()
        except urllib.error.HTTPError as e:
            print(f"Błąd analizy wizyjnej: {e}")
            if e.code == 404 and not self._vision_warned:
                self._vision_warned = True
                self.append_chat("System", f"⚠️ Brak modelu wizyjnego. Uruchom: "
                                           f"ollama pull {VISION_MODEL.split(':')[0]}")
            return None
        except Exception as e:
            print(f"Błąd analizy wizyjnej: {e}")
            return None

    def screen_busy(self):
        return (self.turn_lock.locked() or self.processing or self.user_speaking
                or self.pending_active() or time.time() < self.mute_until)

    def do_screen_check(self):
        use_cam = USE_WEBCAM and CV2_AVAILABLE and random.random() < WEBCAM_CHANCE
        img = self.capture_webcam() if use_cam else self.capture_screen()
        if img is None:
            return
        desc = self.analyze_image(self.encode_image_to_base64(img), CAM_PROMPT if use_cam else SCREEN_PROMPT)
        print(f"[{'kamerka' if use_cam else 'ekran'}] {desc}")
        if not desc or desc.strip().upper().startswith("NOTHING"):
            return
        if not use_cam and self.last_screen_desc and similar(desc, self.last_screen_desc):
            return   # to samo co ostatnio - nie komentuj drugi raz
        if self.screen_busy():
            return   # w międzyczasie zaczęła się rozmowa
        hint = (CAM_HINT if use_cam else SCREEN_HINT).format(desc=desc, lang=LANGS[self.lang]["lang_name"])
        if self.run_turn(hint=hint, label="Waifu 👁️", kind="screen") and not use_cam:
            self.last_screen_desc = desc

    def screen_loop(self):
        if not SCREEN_AVAILABLE:
            return
        while self.running:
            for _ in range(random.randint(SCREEN_MIN_DELAY, SCREEN_MAX_DELAY)):
                if not self.running:
                    return
                time.sleep(1)
            if not self.screen_on or self.screen_busy():
                continue
            try:
                self.do_screen_check()
            except Exception as e:
                print(f"Błąd w obserwacji ekranu: {e}")

    # ---------- ekspresje / emocje ----------
    def pick_expressions(self, emotion):
        manual = EMOTION_EXPRESSIONS.get(emotion)
        if manual:
            names = [manual] if isinstance(manual, str) else list(manual)
            return [self.expr_ids[n] for n in names if n in self.expr_ids]
        for name, eid in self.expr_ids.items():
            low = name.lower()
            if any(h in low for h in EXPRESSION_HINTS.get(emotion, [])):
                return [eid]
        return []

    def clear_expressions(self):
        if self.model is None:
            return
        for fn in ("ResetExpression", "ResetExpressions"):
            try:
                getattr(self.model, fn)()
            except Exception:
                pass

    def apply_emotion(self, emotion, duration):
        self.emotion = emotion
        self.emotion_until = time.time() + duration
        if self.model is None:
            return
        try:
            self.clear_expressions()
            for i, eid in enumerate(self.pick_expressions(emotion)):
                if i == 0:
                    self.model.SetExpression(eid)
                else:
                    self.model.AddExpression(eid)
        except Exception as e:
            print(f"Błąd ustawiania emocji '{emotion}': {e}")

    def current_pose_name(self, now):
        if self.state == "listening":
            return "listening"
        if self.state == "thinking":
            return "thinking"
        if self.emotion != "neutral" and now < self.emotion_until:
            return self.emotion
        if self.state == "idle" and (now < self.awaiting_until or self.pending_active()):
            return "waiting"
        return "neutral"

    # ---------- Live2D ----------
    def register_expressions(self):
        model_dir = Path(MODEL_PATH).parent
        files = sorted(model_dir.rglob("*.exp3.json"))
        for i, p in enumerate(files):
            name = p.name[:-len(".exp3.json")]
            eid = f"x{i}"
            try:
                self.model.LoadExtraExpression(eid, str(p))
                self.expr_ids[name] = eid
            except Exception as e:
                print(f"Nie wczytano ekspresji {p.name}: {e}")
        try:
            for eid in self.model.GetExpressions():
                self.expr_ids.setdefault(eid, eid)
        except Exception:
            pass
        print("Ekspresje:", list(self.expr_ids))
        for emo in EXPRESSION_HINTS:
            print(f"  {emo} -> {self.pick_expressions(emo) or None}")

    def init_live2d_window(self):
        try:
            if not os.path.exists(MODEL_PATH):
                msg = f"Brak pliku modelu: {os.path.abspath(MODEL_PATH)}"
                print(msg)
                self.append_chat("System", msg)
                return

            pygame.init()
            pygame.display.gl_set_attribute(pygame.GL_ALPHA_SIZE, 8)
            pygame.display.set_mode((OVERLAY_W, OVERLAY_H), DOUBLEBUF | OPENGL | NOFRAME)
            pygame.display.set_caption(OVERLAY_TITLE)

            try:
                from pygame._sdl2.video import Window
                self.win = Window.from_display_module()
                self.win.position = OVERLAY_START_POS
                print("Pozycja okna:", self.win.position, "| ekran Tk:",
                      self.root.winfo_screenwidth(), "x", self.root.winfo_screenheight())
            except Exception as e:
                print(f"Przeciąganie okna niedostępne: {e}")

            if ALWAYS_ON_TOP:
                try:
                    subprocess.Popen(["wmctrl", "-r", OVERLAY_TITLE, "-b", "add,above,skip_taskbar"],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
                except FileNotFoundError:
                    print("wmctrl nie jest zainstalowany - okno nie będzie 'zawsze na wierzchu'.")

            live2d.init()
            live2d.glInit()

            self.model = live2d.Model()
            self.model.LoadModelJson(MODEL_PATH)
            self.model.Resize(OVERLAY_W, OVERLAY_H)
            for name, args in (("SetScale", (self.scale,)), ("SetOffset", (0.0, 0.0)),
                               ("SetAutoBlink", (True,)), ("SetAutoBreath", (True,))):
                if hasattr(self.model, name):
                    getattr(self.model, name)(*args)

            try:
                self.param_ids = set(self.model.GetParamIds())
            except Exception as e:
                print(f"GetParamIds nie działa: {e}")
            missing = sorted({k for p in POSES.values() for k in p} - self.param_ids)
            if self.param_ids and missing:
                print("Parametry z póz, których model nie ma (pomijam):", missing)

            self.register_expressions()

            print("Model Live2D załadowany pomyślnie! (T = przezroczystość, Esc = wyjście)")
            self.live2d_running = True
            self.last_t = time.time()
            self.update_live2d()
        except Exception as e:
            import traceback
            traceback.print_exc()
            self.append_chat("System", f"Błąd inicjalizacji Live2D: {e}")

    def handle_events(self):
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                return False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    return False
                elif event.key == pygame.K_t:
                    self.transparent = not self.transparent
                    print("Przezroczystość:", self.transparent)
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if event.button == 1:
                    self.dragging = True
                    self.drag_moved = False
                    self.drag_start_ptr = (self.root.winfo_pointerx(), self.root.winfo_pointery())
                    self.drag_start_pos = tuple(self.win.position) if self.win else (0, 0)
                elif event.button == 3:
                    self.toggle_chat()
            elif event.type == pygame.MOUSEBUTTONUP and event.button == 1:
                if self.dragging and not self.drag_moved:
                    self.apply_emotion("happy", 3.0)  # kliknięcie w postać
                self.dragging = False
            elif event.type == pygame.MOUSEWHEEL:
                self.scale = clamp(self.scale + event.y * 0.05, 0.4, 2.0)
                if hasattr(self.model, "SetScale"):
                    self.model.SetScale(self.scale)
        return True

    def toggle_chat(self):
        if self.chat_visible:
            self.root.withdraw()
        else:
            self.root.deiconify()
        self.chat_visible = not self.chat_visible

    def apply_params(self, now, dt):
        px, py = self.root.winfo_pointerx(), self.root.winfo_pointery()
        wx, wy = (self.win.position if self.win else (0, 0))
        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        nx = clamp((px - (wx + OVERLAY_W / 2)) / (sw / 2), -1, 1)
        ny = clamp((py - (wy + OVERLAY_H / 2)) / (sh / 2), -1, 1)

        name = self.current_pose_name(now)
        target = dict(POSES.get(name, {}))
        k = 1.0 if name == "neutral" else 0.35
        add = {
            "ParamAngleX": nx * 25 * k + math.sin(now * 0.7) * 3,
            "ParamAngleY": -ny * 15 * k,
            "ParamEyeBallX": nx * k,
            "ParamEyeBallY": -ny * k,
            "ParamBodyAngleX": nx * 6 * k,
        }
        for key, val in add.items():
            target[key] = target.get(key, 0.0) + val
        if Lip.active:
            target["ParamAngleZ"] = target.get("ParamAngleZ", 0.0) + math.sin(now * 5) * 3
        target["ParamMouthOpenY"] = Lip.level(now) * 0.95

        for key in set(self.pose) | set(target):
            cur = self.pose.get(key, 0.0)
            cur += (target.get(key, 0.0) - cur) * min(1.0, dt * (25 if key == "ParamMouthOpenY" else 8))
            if key not in target and abs(cur) < 0.001:
                self.pose.pop(key, None)
            else:
                self.pose[key] = cur

        try:
            for key, val in self.pose.items():
                if self.param_ids and key not in self.param_ids:
                    continue
                self.model.SetParamById(key, float(val), 1.0)
        except Exception as e:
            if not self.param_error_shown:
                print(f"SetParamById nie działa: {e}")
                self.param_error_shown = True

    def update_live2d(self):
        if not self.live2d_running:
            return
        try:
            now = time.time()
            dt = min(now - self.last_t, 0.05)
            self.last_t = now

            if not self.handle_events():
                self.shutdown_live2d()
                return

            if self.dragging and self.win:
                px, py = self.root.winfo_pointerx(), self.root.winfo_pointery()
                dx, dy = px - self.drag_start_ptr[0], py - self.drag_start_ptr[1]
                if abs(dx) + abs(dy) > 4:
                    self.drag_moved = True
                if self.drag_moved:
                    self.win.position = (self.drag_start_pos[0] + dx, self.drag_start_pos[1] + dy)

            if self.emotion != "neutral" and now > self.emotion_until and self.state != "speaking":
                self.emotion = "neutral"
                self.clear_expressions()

            r, g, b, a = (0.0, 0.0, 0.0, 0.0) if self.transparent else (1.0, 0.90, 0.94, 1.0)
            live2d.clearBuffer(r, g, b, a)

            self.model.Update()
            self.apply_params(now, dt)
            self.model.Draw()
            pygame.display.flip()
        except Exception:
            import traceback
            traceback.print_exc()
            self.live2d_running = False
            return

        self.root.after(16, self.update_live2d)

    def shutdown_live2d(self):
        was_running = self.live2d_running
        self.live2d_running = False
        if not was_running:
            return
        try:
            self.model = None
            live2d.dispose()
            pygame.quit()
        except Exception:
            pass

    def on_close(self):
        self.running = False
        self.shutdown_live2d()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    app = AnimeAIGUI(root)
    root.mainloop()