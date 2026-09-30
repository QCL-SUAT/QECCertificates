#!/usr/bin/env python
r"""Portability gate: the repository must build and run on any machine.

Fails (exit 1) on machine-coupled path configuration in tracked sources:

  1. MACHINE PATHS -- absolute paths that exist only on one machine:
     `C:\...`, `C:/...`, `C:\\...` (the escaped spelling a tool prints when it
     shows its own raw output), `/c/...`, `/Users/<name>/...`,
     `/home/<name>/...`, `/tmp/...`, `AppData`, `miniforge3`, `anaconda3`,
     `Desktop/`, `~/lean`.  A placeholder standing where the name goes
     (`/Users/<user>/...`, or the drive form with `<user>`) is a shape rather
     than a location and passes, in both spellings.
  2. RELATIVE DATA I/O -- a bare filename (no directory separator) passed to a
     file call (`open`, `json.load`, `np.load`, `glob.glob`, ...) is resolved
     against the *working directory*, so the script silently reads or writes a
     different file depending on where it is launched.  Data paths must be
     anchored on the script's own location (`os.path.join(HERE, ...)` in
     Python, `joinpath(@__DIR__, ...)` in Julia).
  3. CWD-DEPENDENT IDIOMS -- `os.path.abspath('.')` and `os.getcwd()` used to
     build project paths assume a particular launch directory.
  4. INCOMPLETE CHECKOUT -- a tracked file is absent from the working tree.  A
     checkout missing tracked files is not the same repository, and the failure
     is silent in the worst way: every gate reads tracked files, and a scanner
     that reads fewer of them prints exactly the same summary line.  Five
     tracked files (all three LICENSEs, PROJECT_LOG.md and AGENT_METRICS.md)
     were gone from the working tree and the whole nine-step chain reported
     green.  This rule is the source-side twin of the rule the
     chain already applies to products: an input that is absent is a failure,
     never a skip.
  5. NON-PORTABLE DEPENDENCY DECLARATION -- a tracked `lake-manifest.json` lists
     any package that is not a remote git dependency, or that carries a
     directory field.  `.json` is excluded from the text scan (data files
     legitimately hold arbitrary strings), so this one JSON file, which is
     configuration rather than data, gets its own narrow rule.  It is the
     failure mode a fresh checkout cannot show you: a path dependency builds
     fine on the machine that has that directory and hard-fails everywhere else,
     which is exactly how a repository ends up green locally and broken for
     every reader.
  6. CONTROL BYTES IN A TEXT SOURCE -- any C0 byte other than LF.  A non-raw
     string in a writer script turns a command into a control character and
     nothing else notices (`\binom` becomes 0x08 + "inom", `\times` becomes 0x09
     + "imes"); this repository has recorded that family four times over; the
     workspace root README was damaged that way and a probe written to verify
     it "passed" because the probe string was folded identically.  Zero false
     positives in this scope as measured: no tracked text source here contains
     a TAB.

Usage:
    python tools/check_portability.py [--list-allowlist] [--self-test]

The scan is scoped to this project directory by default.  Two options let the
workspace-root entry (`<workspace>/tools/check_portability.py`) reuse **this same
implementation** with the opposite scope -- the part no project gate covers
(the workspace root's own files and `项目申请/`):

    --root PATH        scan PATH instead of this project directory
    --exclude PREFIX   skip tracked paths starting with PREFIX (repeatable)

Exits 0 when clean, 1 when anything is found.  Run it from anywhere: the
project directory is located from this file's own path, one level up (which is the very
discipline it enforces).
"""

import ast
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import warnings

# Scanning a source file with `ast.parse` surfaces its own invalid-escape
# SyntaxWarnings (e.g. a docstring containing `\p`).  Those belong to the file
# being scanned, not to this gate -- keep the report to findings only.
warnings.filterwarnings("ignore", category=SyntaxWarning)

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)   # the project dir; this script lives in tools/

# Paths that belong to another project's own gate.  The workspace-root entry
# sets these to the sibling project directories so that this implementation,
# which is the only copy of these rules, can cover the complement instead of
# duplicating them -- a third copy would drift, and this repository has seven
# recorded instances of a duplicated truth going stale unnoticed.
EXCLUDE_PREFIXES = []


def excluded_rel(rel):
    r = rel.replace("\\", "/")
    for p in EXCLUDE_PREFIXES:
        p = p.replace("\\", "/").rstrip("/")
        if r == p or r.startswith(p + "/"):
            return True
    return False


def parse_args(argv):
    """Consume --root/--exclude; return the remaining argv."""
    global ROOT
    rest, i = [], 0
    while i < len(argv):
        a = argv[i]
        if a == "--root" and i + 1 < len(argv):
            ROOT = os.path.abspath(argv[i + 1]); i += 2
        elif a.startswith("--root="):
            ROOT = os.path.abspath(a.split("=", 1)[1]); i += 1
        elif a == "--exclude" and i + 1 < len(argv):
            EXCLUDE_PREFIXES.append(argv[i + 1]); i += 2
        elif a.startswith("--exclude="):
            EXCLUDE_PREFIXES.append(a.split("=", 1)[1]); i += 1
        else:
            rest.append(a); i += 1
    return rest

# Text sources worth scanning.  Data (.json) and reference PDFs are excluded:
# they legitimately contain arbitrary strings.  `.mmd` is Mermaid source, i.e.
# authored text like `.md`, and is scanned for that reason (the workspace holds
# one, under 项目申请/figures/).  Files with no extension at all -- the three
# LICENSEs, .gitignore, .gitattributes -- are not text-scanned; rule 4 still
# covers their presence, which is the failure they actually had.
SCAN_EXT = {".py", ".jl", ".sh", ".lean", ".toml", ".tex", ".tikz", ".md",
            ".mmd", ".yml", ".yaml", ".cfg", ".txt"}

DATA_EXT = ("json", "jsonl", "csv", "npy", "npz", "txt", "dat", "pkl", "f64",
            "i32", "h5", "tsv",
            # figure outputs: the paper includes these PDFs directly, so a
            # cwd-relative savefig would silently write the figure elsewhere
            "pdf", "png", "svg", "eps")
# A relative data path: has a data extension, no whitespace (which excludes
# prose such as "wrote x.json"), and is not absolute.  Slash-separated paths
# such as "figures/fig_l1/out.json" are included -- they are just as
# cwd-dependent as a bare filename, they merely assume a particular launch dir.
REL_PATH_RE = re.compile(r"^(?![~/]|[A-Za-z]:)[^\\\s]+\.(" + "|".join(DATA_EXT) + r")$")

FILE_ARG = {
    "open": 0,
    "json.load": 0, "json.dump": 1,
    "glob.glob": 0, "glob.iglob": 0,
    "pickle.load": 0, "pickle.dump": 1,
    "np.load": 0, "np.save": 0, "np.savez": 0, "np.savetxt": 0,
    "np.loadtxt": 0, "np.genfromtxt": 0, "np.fromfile": 0,
    "pd.read_csv": 0, "pd.read_json": 0,
    "shutil.copy": 0, "shutil.copyfile": 0,
    "sp.load_npz": 0, "sp.save_npz": 0,
}
FILE_KW = {"file", "fname", "filename", "path"}

# The builtin text open and its standard-library spellings.  The encoding rule
# is about *text mode* defaults, so only these names count.  Matching any
# attribute whose last component is `open` also caught `Image.open(...)`, which
# reads images and takes no encoding argument: a false positive that stayed
# invisible for as long as only the two project scopes were scanned (neither
# contains such a call), and surfaced the first time the workspace-root scope
# read 项目申请/.  Add a real text open by extending this set, never by
# loosening the match.
TEXT_OPEN_NAMES = {"open", "io.open", "_io.open", "codecs.open"}

# Julia file calls whose first argument is a path.  `readline` and `read!` are
# included because the K=100/K=160 arbitration scripts load their raw CSC dumps
# through exactly those.
JL_FILE_ARG = {"open", "readline", "readlines", "read", "read!", "readdlm",
               "writedlm", "include", "load", "save", "JSON3.read",
               "JSON3.write", "CSV.read", "CSV.write"}

MACHINE_PATH_PATTERNS = [
    # A drive path must have at least TWO segments, and the drive letter must
    # not follow a word character.  Without both guards this pattern matches
    # `https://` and LaTeX such as `I(A:\bar A)` / `X_B:\ I_A`, which buries
    # the real findings in false positives.
    #
    # The separator accepts ONE OR TWO backslashes.  One is the ordinary
    # spelling; two is what a tool prints when it shows its raw output -- a glob
    # result, a JSON string -- and a one-backslash pattern reads the second
    # backslash as the name, so that form would pass this gate in silence.
    # Measured: a record quoting such output carried a real user name
    # and every run was green.  The two-segment guard above still keeps `C:\\x`
    # (one segment) and LaTeX out.
    #
    # The trailing lookahead keeps placeholders legal, in step with the POSIX
    # rules below: the drive form is flagged only when at least one more name
    # character follows, so a path written as evidence with `<user>` where the
    # name goes is a shape and not a location -- the same reason the record's
    # `/Users/<user>/...` lines pass.  Without it the group stops after the
    # second segment and the placeholder never gets a say.
    (re.compile(r"(?<![A-Za-z0-9_])[A-Za-z]:[\\/]{1,2}(?:[A-Za-z0-9_.\-]+[\\/]{1,2})+"
                r"(?=[A-Za-z0-9_.\-])"),
     "Windows absolute path"),
    (re.compile(r"/c/(Users|ProgramData|Program Files|Windows|lean)\b"), "MSYS Windows path"),
    (re.compile(r"/Users/[A-Za-z0-9._-]+/"), "macOS absolute path"),
    (re.compile(r"/home/[A-Za-z0-9._-]+/"), "Linux absolute path"),
    (re.compile(r"(miniforge3|anaconda3|AppData[/\\])"), "machine-specific install path"),
    (re.compile(r"\bDesktop/"), "machine-specific user path"),
    (re.compile(r"~/lean\b"), "machine-specific shared-library path"),
    (re.compile(r"(?<![\w/])/tmp/"), "machine-specific temp path"),
]

CWD_IDIOM_PATTERNS = [
    (re.compile(r"os\.path\.abspath\(\s*['\"]\.['\"]\s*\)"), "os.path.abspath('.')"),
    (re.compile(r"os\.getcwd\(\)"), "os.getcwd() used to build a path"),
    # sys.path.insert with a *literal* directory is resolved against the CWD.
    # (The anchored forms take no string literal, so they never match here.)
    (re.compile(r"""sys\.path\.insert\(\s*\d+\s*,\s*['"][^'"]+['"]\s*\)"""),
     "sys.path.insert with a cwd-relative literal"),
]

# Documented defaults and self-references only.  Each entry is
# (path substring, line-contains substring, reason).  Keep this list short and
# justified -- anything else belongs fixed, not allowlisted.
ALLOWLIST = [
    # `setup_links.sh` *searches* a candidate list of shared-library roots so
    # that a developer machine needs no configuration.  Those paths are the
    # script's probe targets and an error message, never a dependency: the
    # script is optional, exits 0 when nothing is found, and `LEAN_GLOBAL`
    # overrides the whole list.
    ("setup_links.sh", "/c/lean",
     "search list of shared-library roots; optional script, overridable via LEAN_GLOBAL"),
    (".gitattributes", None, "records that blobs are LF, contains no paths"),
    ("tools/check_portability.py", None, "this file: defines the patterns it reports"),
]


def allowlisted(rel, line, reason_hint=None):
    for sub, needle, _why in ALLOWLIST:
        if sub in rel.replace("\\", "/"):
            if needle is None or (line is not None and needle in line):
                return True
    return False


def tracked_files():
    try:
        # `--cached --others --exclude-standard` = tracked + untracked-but-not-ignored.
        # Plain `ls-files` is blind to a brand-new script until it is staged, so a
        # machine-coupled path could sit in the working tree while the gate is green.
        #
        # `-z` for the same reason `missing_tracked_files()` needs it, and the
        # reason is not decoration: without it git C-quotes non-ASCII paths
        # (`项目申请/x.md` comes back as `"\351\241..."`), the quoted string does
        # not resolve on disk, `read_lines` returns None, and the file is
        # **silently skipped** -- the scanner reads fewer files and prints the
        # identical summary line.  Measured on the workspace-root
        # scope: a coupled path injected into two files under `项目申请/` was
        # not reported until this was fixed, while the root's own ASCII files
        # were scanned fine.  In the project scopes the relative paths happen to
        # be ASCII, so the defect was invisible there.
        out = subprocess.run(["git", "-C", ROOT, "ls-files", "--cached", "--others",
                              "--exclude-standard", "-z"],
                             capture_output=True, check=True).stdout
        files = [raw.decode("utf-8", "surrogateescape") for raw in out.split(b"\0")]
        return [f for f in files if f.strip() and not excluded_rel(f)]
    except Exception:
        files = []
        for base, dirs, names in os.walk(ROOT):
            dirs[:] = [d for d in dirs if d not in (".git", ".lake", "__pycache__")]
            for n in names:
                files.append(os.path.relpath(os.path.join(base, n), ROOT))
        return files


def read_lines(rel):
    path = os.path.join(ROOT, rel)
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError:
        return None
    if b"\0" in raw[:4096]:
        return None
    return raw.decode("utf-8", errors="replace").replace("\r\n", "\n").split("\n")


# Inline math in LaTeX-heavy docs (`$h:=\{j:\delta_j\ne0\pmod p\}$`) trips the
# drive-path pattern on the `h:` + two segments shape.  Strip `$...$` spans
# before matching; code and paths never live inside inline math.
MATH_SPAN = re.compile(r"\$[^$]*\$")


def scan_control_bytes(rel, findings):
    """C0 control bytes other than LF in a text source.

    This is the batch-write trap this repository keeps re-learning: a non-raw
    string in a writer script turns a command into a control character, and
    nothing else notices.  Measured on the workspace root README, where a
    repair script wrote ``\\binom`` as 0x08 + "inom" and ``\\times`` as
    0x09 + "imes": LaTeX renders it, Markdown shows it, and the probe written to
    verify it "confirmed" the text because the probe string was folded the same
    way -- a check that cannot distinguish.

    Zero false positives in this repository's text scope as measured: not one
    of its tracked text sources contains a TAB, so TAB is flagged along with
    the rest.  Only SCAN_EXT files are read, so images, PDFs and `.json` data
    are untouched.
    """
    path = os.path.join(ROOT, rel)
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError:
        return
    for i, b in enumerate(raw):
        if b < 32 and b != 10:
            line = raw.count(b"\n", 0, i) + 1
            ctx = raw[max(0, i - 18):i + 18].decode("utf-8", "replace")
            if b == 13:
                why = ("carriage return: this repository's text is LF.  The blob may "
                       "already be LF -- only the working copy drifted, which `git "
                       "status` hides because the attributes normalise it -- so "
                       "`git checkout -- <path>` restores it; the usual cause is a "
                       "Windows tool writing CRLF into a checked-out file.")
            else:
                why = ("a folded escape in a batch write does this silently: ...%s..."
                       % ctx.replace("\n", " "))
            findings.append((rel, line, "control byte 0x%02x -- %s" % (b, why)))
            return          # one per file is enough to act on


def scan_text_paths(rel, lines, findings):
    for i, line in enumerate(lines, 1):
        line = MATH_SPAN.sub("$…$", line)
        for pat, what in MACHINE_PATH_PATTERNS:
            if pat.search(line):
                if allowlisted(rel, line):
                    continue
                findings.append((rel, i, f"machine-specific path ({what}): "
                                         f"{line.strip()[:100]}"))
                break


def dotted(node):
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = dotted(node.value)
        return f"{base}.{node.attr}" if base else None
    return None


def is_bare_const(node):
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and REL_PATH_RE.match(node.value) is not None)


def parents_of(tree):
    par = {}
    for node in ast.walk(tree):
        for child in ast.iter_child_nodes(node):
            par[id(child)] = node
    return par


def is_anchored(node, par):
    """True if `node` sits inside an os.path.join / joinpath / Path() call."""
    cur = par.get(id(node))
    while cur is not None:
        if isinstance(cur, ast.Call):
            fn = dotted(cur.func) or ""
            if fn.endswith("makedirs") or fn.endswith("exists") or fn.endswith("dirname"):
                cur = par.get(id(cur))
                continue
            if "path.join" in fn or fn == "joinpath" or fn.endswith("Path"):
                return True
        cur = par.get(id(cur))
    return False


def scan_python(rel, src, findings):
    try:
        tree = ast.parse(src)
    except SyntaxError as e:
        findings.append((rel, e.lineno or 0, f"cannot parse: {e}"))
        return
    par = parents_of(tree)

    def args_of(call):
        out = []
        idx = FILE_ARG[dotted(call.func)]
        if len(call.args) > idx:
            out.append(call.args[idx])
        for kw in call.keywords:
            if kw.arg in FILE_KW:
                out.append(kw.value)
        return out

    io_names = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and dotted(node.func) in FILE_ARG:
            for a in args_of(node):
                if is_bare_const(a) and not is_anchored(a, par):
                    findings.append((rel, a.lineno,
                                     f"data file {a.value!r} resolved against the "
                                     f"working directory; anchor it on HERE"))
                elif isinstance(a, ast.Name):
                    io_names.add(a.id)

    if not io_names:
        return
    # filenames bound to a name that is used as an I/O argument
    for node in ast.walk(tree):
        targets = []
        if isinstance(node, ast.Assign):
            targets = node.targets
        elif isinstance(node, ast.AnnAssign):
            targets = [node.target]
        if targets and is_bare_const(node.value):
            for t in targets:
                if isinstance(t, ast.Name) and t.id in io_names and not is_anchored(node.value, par):
                    findings.append((rel, node.value.lineno,
                                     f"{t.id} = {node.value.value!r} is an I/O path "
                                     f"resolved against the working directory"))
    # for-loops over literal filename tuples whose loop var is an I/O argument
    for node in ast.walk(tree):
        if isinstance(node, ast.For) and isinstance(node.iter, (ast.List, ast.Tuple)):
            tnames = set()

            def names_of(t):
                if isinstance(t, ast.Name):
                    tnames.add(t.id)
                elif isinstance(t, (ast.Tuple, ast.List)):
                    for e in t.elts:
                        names_of(e)
            names_of(node.target)
            if tnames & io_names:
                for sub in ast.walk(node.iter):
                    if is_bare_const(sub) and not is_anchored(sub, par):
                        findings.append((rel, sub.lineno,
                                         f"data file {sub.value!r} in a loop feeding "
                                         f"an I/O call, resolved against the working "
                                         f"directory"))


def scan_python_encoding(rel, tree, findings):
    """Text-mode `open()` must pin `encoding=` (and `newline=` when writing).

    Python's text mode defaults to the *platform locale* encoding -- GBK on a
    Chinese Windows box, UTF-8 on macOS/Linux -- and to locale newline
    translation.  The same script then decodes a UTF-8 file with GBK (raising
    UnicodeDecodeError) or writes CRLF, depending only on which machine ran it.
    Nothing in the code looks wrong, which is exactly why it needs a gate.
    """
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        fn = dotted(node.func) or ""
        if fn not in TEXT_OPEN_NAMES:
            continue
        kws = {k.arg for k in node.keywords}
        mode = ""
        if len(node.args) > 1 and isinstance(node.args[1], ast.Constant):
            mode = node.args[1].value
        if "b" in mode:
            continue
        if "encoding" not in kws:
            findings.append((rel, node.lineno,
                             "text open() without explicit encoding= -- the "
                             "platform locale default (GBK on Windows, UTF-8 "
                             "elsewhere) decides what is read or written"))
        if ("w" in mode or "a" in mode or "x" in mode) and "newline" not in kws:
            findings.append((rel, node.lineno,
                             "text open() in write mode without newline=\"\\n\" "
                             "-- the platform newline convention leaks into the "
                             "file (CRLF on Windows)"))


def scan_julia(rel, lines, findings):
    for i, line in enumerate(lines, 1):
        if line.lstrip().startswith("#"):
            continue
        for fn in JL_FILE_ARG:
            m = re.search(r"\b" + re.escape(fn) + r"\s*\(\s*(['\"])([^'\"]+)\1", line)
            if m and REL_PATH_RE.match(m.group(2)) and "@__DIR__" not in line:
                findings.append((rel, i,
                                 f"data file {m.group(2)!r} resolved against the "
                                 f"working directory; use joinpath(@__DIR__, ...)"))
                break


LAKE_MANIFEST = "lake-manifest.json"
REMOTE_URL = re.compile(r"(?:https?|ssh|git)://|^git@")


def scan_lake_manifest(rel, findings):
    """Rule 5: every package a tracked Lake manifest lists must be portable.

    A path dependency is written into the manifest as `"type": "path"` with a
    `dir`, so this catches it no matter which file declared it.  Revisions must
    be full commit hashes: a tag or a short hash is not content-addressed and
    makes Lake resolve over the network (which fails exactly where the network
    is restricted).
    """
    with open(os.path.join(ROOT, rel), "rb") as fh:
        try:
            data = json.loads(fh.read().decode("utf-8"))
        except Exception as exc:              # unreadable, or not JSON at all
            findings.append((rel, 0, f"unreadable as JSON: {exc}"))
            return
    packages = data.get("packages") if isinstance(data, dict) else None
    if not isinstance(packages, list):
        findings.append((rel, 0, "no `packages` list -- is this a Lake manifest?"))
        return
    for i, pkg in enumerate(packages):
        if not isinstance(pkg, dict):
            findings.append((rel, 0, f"package #{i} is not an object"))
            continue
        name = pkg.get("name") or f"#{i}"
        kind = pkg.get("type")
        if kind != "git":
            findings.append((rel, 0, f"dependency {name} is declared type={kind!r}; only a "
                                     f"git dependency is portable -- a path dependency "
                                     f"builds only on the machine that has that directory"))
        url = pkg.get("url")
        if not (isinstance(url, str) and REMOTE_URL.search(url)):
            findings.append((rel, 0, f"dependency {name}: url {url!r} is not a remote URL"))
        for key in ("dir", "path"):
            if key in pkg:
                findings.append((rel, 0, f"dependency {name}: carries a {key!r} field "
                                         f"({pkg[key]!r}) -- machine-coupled"))
        if kind == "git":
            rev = pkg.get("rev")
            if not (isinstance(rev, str) and re.fullmatch(r"[0-9a-f]{40}", rev)):
                findings.append((rel, 0, f"dependency {name}: rev={rev!r} is not a "
                                         f"40-character commit hash"))
        for key in ("inputRev",):
            val = pkg.get(key)
            if isinstance(val, str) and val and not re.fullmatch(r"[0-9a-f]{40}", val):
                findings.append((rel, 0, f"dependency {name}: {key}={val!r} is not a "
                                         f"40-character commit hash (a tag or a short "
                                         f"hash is not content-addressed)"))


def missing_tracked_files():
    """Tracked entries that are present in the index but absent on disk.

    `-z` is not decoration: `git ls-files` C-quotes non-ASCII paths (a CJK
    filename comes back as `"\\350\\256\\272..."`), and anything that splits the
    quoted form on whitespace reports misses that are not there -- a hand-built
    loop over the plain output once counted 444 absent files in this repository
    when the true number was five.
    """
    try:
        out = subprocess.run(["git", "-C", ROOT, "ls-files", "--cached", "-z"],
                             capture_output=True, check=True).stdout
    except Exception:
        return []
    missing = []
    for raw in out.split(b"\0"):
        if not raw:
            continue
        rel = raw.decode("utf-8", "surrogateescape")
        if excluded_rel(rel):
            continue          # another project's gate owns that path
        if not os.path.lexists(os.path.join(ROOT, rel)):
            missing.append(rel)
    return sorted(missing)


def self_test():
    """Controls for the completeness rule, in a throwaway repository.

    The script is copied into a fresh `git init` tree, so the injected deletion
    happens somewhere disposable; the repository being checked is never touched.
    """
    here = os.path.abspath(__file__)
    ok = True
    with tempfile.TemporaryDirectory() as td:
        tools = os.path.join(td, "tools")
        os.makedirs(tools)
        probe = os.path.join(tools, "check_portability.py")
        shutil.copyfile(here, probe)

        def write(rel, text):
            with open(os.path.join(td, rel), "w", encoding="utf-8", newline="\n") as fh:
                fh.write(text)

        def run(*extra):
            return subprocess.run([sys.executable, probe, *extra], capture_output=True,
                                  text=True, encoding="utf-8", errors="replace")

        def git(*args):
            return subprocess.run(["git", "-C", td, *args], capture_output=True,
                                  text=True, encoding="utf-8", errors="replace")

        write("notes.md", "A tracked file that carries nothing machine-coupled.\n")
        git("init", "-q")
        git("add", "-A")
        git("-c", "user.email=probe@example.invalid", "-c", "user.name=probe",
            "commit", "-qm", "probe")

        r = run()
        passed = r.returncode == 0
        print(f"  baseline (intact checkout)      -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        os.remove(os.path.join(td, "notes.md"))
        r = run()
        passed = r.returncode == 1 and "notes.md" in r.stdout
        print(f"  a tracked file deleted         -> exit {r.returncode}, names it: {passed}"
              f" (want 1/True)")
        ok &= passed

        write("notes.md", "A tracked file that carries nothing machine-coupled.\n")
        r = run()
        passed = r.returncode == 0
        print(f"  restored                       -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        # Controls for --root/--exclude: the scoping the workspace-root entry
        # relies on.  The same finding must be reported at the top level and
        # skipped under an excluded prefix, and the completeness rule must
        # respect the prefix the same way -- otherwise the root entry would
        # report the sibling projects a second time, under another gate's name.
        os.makedirs(os.path.join(td, "sib"), exist_ok=True)
        write("sib/notes.md", "see /Users/asm/lean/packages\n")
        write("mine.md", "see /Users/asm/lean/packages\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 1 and "sib/notes.md" in r.stdout and "mine.md" in r.stdout
        print(f"  unscoped: both reported        -> exit {r.returncode}, both named: {passed}"
              f" (want 1/True)")
        ok &= passed

        r = run("--exclude", "sib/")
        passed = (r.returncode == 1 and "sib/notes.md" not in r.stdout
                  and "mine.md" in r.stdout)
        print(f"  --exclude sib/: only mine.md   -> exit {r.returncode}, sib silent: {passed}"
              f" (want 1/True)")
        ok &= passed

        write("mine.md", "A tracked file that carries nothing machine-coupled.\n")
        git("add", "-A")
        r = run("--exclude", "sib/")
        passed = r.returncode == 0
        print(f"  coupled only under the prefix  -> exit {r.returncode}, want 0: {passed}"
              f"  (green only because the prefix is skipped)")
        ok &= passed

        os.remove(os.path.join(td, "sib", "notes.md"))
        r = run("--exclude", "sib/")
        passed = r.returncode == 0
        print(f"  missing file, excluded prefix  -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        r = run()
        passed = r.returncode == 1 and "sib/notes.md" in r.stdout
        print(f"  same missing file, unscoped    -> exit {r.returncode}, named: {passed}"
              f" (want 1/True)")
        ok &= passed

        # Leave the tree carrying nothing coupled: the rule-5 controls below run
        # without --exclude, so a leftover would fail them for the wrong reason.
        write("sib/notes.md", "A tracked file that carries nothing machine-coupled.\n")
        git("add", "-A")

        # A non-ASCII path must be scanned, not skipped.  Without `-z` git
        # C-quotes it, the quoted name resolves to nothing, and the gate reads
        # fewer files while printing the same summary line -- measured on the
        # workspace-root scope, where the relative paths carry CJK directory
        # names and the project scopes' do not.
        os.makedirs(os.path.join(td, "项目申请"), exist_ok=True)
        write("项目申请/sib-notes.md", "see /Users/asm/lean/packages\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 1 and "sib-notes.md" in r.stdout
        print(f"  non-ASCII path is scanned      -> exit {r.returncode}, named: {passed}"
              f" (want 1/True)")
        ok &= passed

        # Controls for the control-byte rule: a folded escape must be caught, a
        # TAB must be caught (this repository has none), and clean text must not.
        ctl = os.path.join(td, "probe_ctl.md")
        with open(ctl, "wb") as fh:
            fh.write(b"a folded escape: " + bytes([8]) + b"inom{n}{k}\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 1 and "control byte 0x08" in r.stdout
        print(f"  0x08 from a folded escape      -> exit {r.returncode}, caught: {passed}"
              f" (want 1/True)")
        ok &= passed

        with open(ctl, "wb") as fh:
            fh.write(b"a TAB " + bytes([9]) + b" in text\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 1 and "control byte 0x09" in r.stdout
        print(f"  a TAB in text                  -> exit {r.returncode}, caught: {passed}"
              f" (want 1/True)")
        ok &= passed

        os.remove(ctl)
        git("add", "-A")

        write("项目申请/sib-notes.md", "A tracked file that carries nothing machine-coupled.\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 0
        print(f"  non-ASCII path cleaned         -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        # Controls for the encoding rule's name set, in both directions: a text
        # open without encoding= must be caught, and an attribute that merely
        # ends in `.open` (PIL's Image.open, which takes no encoding) must not.
        write("probe_enc.py", "open('x.txt')\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 1 and "without explicit encoding" in r.stdout
        print(f"  text open() without encoding   -> exit {r.returncode}, caught: {passed}"
              f" (want 1/True)")
        ok &= passed

        write("probe_enc.py", "Image.open(buf)\n")
        git("add", "-A")
        r = run()
        passed = r.returncode == 0
        print(f"  Image.open() is not a text open -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        os.remove(os.path.join(td, "probe_enc.py"))
        git("add", "-A")

        # Rule 5 controls: a path dependency must be caught, a git one must not,
        # and a non-content-addressed inputRev must be caught.
        sha = "5ed2965256430c3649e86755f9576b54eca72435"

        def manifest(name, **over):
            entry = {"name": name, "type": "git",
                     "url": "https://github.com/leanprover-community/mathlib4.git",
                     "rev": sha, "inputRev": sha}
            entry.update(over)
            return json.dumps({"name": "probe", "packages": [entry]})

        write(LAKE_MANIFEST, manifest("mathlib"))
        r = run()
        passed = r.returncode == 0
        print(f"  git dependency (manifest)      -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        write(LAKE_MANIFEST, manifest("local", type="path", dir="../elsewhere"))
        r = run()
        passed = r.returncode == 1 and "local" in r.stdout and "path" in r.stdout
        print(f"  path dependency                -> exit {r.returncode}, names it: {passed}"
              f" (want 1/True)")
        ok &= passed

        write(LAKE_MANIFEST, manifest("mathlib", rev="5ed2965", inputRev="v4.34.0"))
        r = run()
        passed = r.returncode == 1 and "40-character" in r.stdout
        print(f"  short rev / tag inputRev       -> exit {r.returncode}, explains: {passed}"
              f" (want 1/True)")
        ok &= passed

        os.remove(os.path.join(td, LAKE_MANIFEST))

        # A machine path, in the two spellings, plus the one form that must stay
        # legal.  Needles are assembled from parts, like every other path this
        # file carries, so the gate does not find its own source.
        bs = chr(92)
        # A clean tree first.  The three cases below must fail (or pass)
        # because of what they inject and nothing else -- and the short-rev
        # control above leaves the manifest in a deliberately invalid state, so
        # without this the two "must be caught" cases would be green whatever
        # the pattern said, and the "must stay legal" one would be red for a
        # reason of its own.  Measured: a control block without this baseline
        # had exactly that defect in the twin file, where the manifest was
        # still on disk.
        manifest_path = os.path.join(td, LAKE_MANIFEST)
        if os.path.exists(manifest_path):
            os.remove(manifest_path)
        r = run()
        passed = r.returncode == 0
        print(f"  baseline before the path cases  -> exit {r.returncode}, want 0: {passed}")
        ok &= passed

        # Each case also stands alone: a file left behind by the previous case
        # would be found by the next run.
        single = "the ordinary spelling: C:" + bs + "Users" + bs + "someone" + bs + "work" + chr(10)
        write("single.md", single)
        r = run()
        passed = r.returncode == 1 and "single.md" in r.stdout and "Windows absolute path" in r.stdout
        print(f"  Windows path (one backslash)    -> exit {r.returncode}, names it: {passed}"
              f" (want 1/True)")
        ok &= passed
        os.remove(os.path.join(td, "single.md"))

        escaped = ("a tool's raw output: C:" + bs * 2 + "Users" + bs * 2 + "someone"
                   + bs * 2 + "work" + chr(10))
        write("escaped.md", escaped)
        r = run()
        passed = r.returncode == 1 and "escaped.md" in r.stdout and "Windows absolute path" in r.stdout
        print(f"  Windows path (escaped, two)     -> exit {r.returncode}, names it: {passed}"
              f" (want 1/True)")
        ok &= passed
        os.remove(os.path.join(td, "escaped.md"))

        # The boundary that keeps evidence quotable: the same shape with a
        # placeholder instead of a name is not a path that resolves anywhere.
        write("placeholder.md", "the shape, with a placeholder: C:" + bs * 2
              + "Users" + bs * 2 + "<user>" + bs * 2 + "work" + chr(10))
        r = run()
        passed = r.returncode == 0
        print(f"  same shape, placeholder name    -> exit {r.returncode}, want 0: {passed}")
        ok &= passed
        os.remove(os.path.join(td, "placeholder.md"))

        if os.path.exists(os.path.join(td, LAKE_MANIFEST)):
            os.remove(os.path.join(td, LAKE_MANIFEST))

    print("SELFTEST: " + ("OK" if ok else "FAILED"))
    return 0 if ok else 1


def main():
    argv = parse_args(sys.argv[1:])
    if "--list-allowlist" in argv:
        for sub, needle, why in ALLOWLIST:
            print(f"{sub}: {why}")
        return 0
    if "--self-test" in argv:
        return self_test()

    findings = []
    for rel in missing_tracked_files():
        findings.append((rel, 0, "tracked file is missing from the working tree; "
                                 "restore it with `git show HEAD:<path> > <path>` "
                                 "(additive: nothing is overwritten)"))
    for rel in tracked_files():
        if os.path.basename(rel) == LAKE_MANIFEST:
            # Configuration, not data: `.json` is out of SCAN_EXT by design, so
            # this one file gets its own rule instead of a text scan.
            scan_lake_manifest(rel, findings)
            continue
        ext = os.path.splitext(rel)[1].lower()
        if ext not in SCAN_EXT:
            continue
        # Before the allowlist skip: the allowlist is about *path and cwd rules*
        # this file's patterns would otherwise report on themselves, not about
        # whether its own bytes are sound.
        scan_control_bytes(rel, findings)
        if allowlisted(rel, None):
            continue
        lines = read_lines(rel)
        if lines is None:
            continue
        src = "\n".join(lines)
        for i, line in enumerate(lines, 1):
            if allowlisted(rel, line):
                continue
            for pat, what in CWD_IDIOM_PATTERNS:
                if pat.search(line):
                    findings.append((rel, i, f"cwd-dependent idiom: {what}"))
                    break
        scan_text_paths(rel, lines, findings)
        if ext == ".py":
            scan_python(rel, src, findings)
            try:
                scan_python_encoding(rel, ast.parse(src), findings)
            except SyntaxError:
                pass  # already reported by scan_python
        elif ext == ".jl":
            scan_julia(rel, lines, findings)

    findings = sorted(set(findings))
    if not findings:
        print("check_portability: OK -- no machine-coupled path configuration found, "
              "and every tracked file is present.")
        return 0
    print(f"check_portability: {len(findings)} finding(s)\n")
    for rel, line, msg in findings:
        print(f"  {rel}:{line}: {msg}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
