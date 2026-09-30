#!/usr/bin/env bash
# 【可选】把 `.lake/packages` 接到**全局共享库**（零副本、零下载的开发姿势）。
#
# 新克隆的机器**不需要**跑这个脚本：`lake build` 会按 lakefile/lake-manifest 的
# git 依赖（pin 40 位 SHA1）自动取得 mathlib + 8 传递包 + LeanQEC + QEC。
# 本脚本只适用于「本机已有一份全局检出、想省一次下载与一次全量编译」的开发机。
#
# 用法（脚本自己会找全局根，无需配置）：
#   ./setup_links.sh
#   LEAN_GLOBAL=/path/to/lean ./setup_links.sh          # 显式指定
#   LEAN_DEPS_MATHLIB=... LEAN_DEPS_PACKAGES=... ./setup_links.sh
#
# 支持的全局布局（两种都自动识别）：
#   (M) macOS/Linux 常见：  $G/mathlib4  +  $G/packages/{aesop,batteries,...}
#   (W) Windows 常见：      $G/mathlib4  +  $G/libs/{Lean-QEC,physlib,QECLean,Lean-QIT}
# 8 个传递包缺失时退回 `<mathlib>/.lake/packages/*`（mathlib 自带的检出）。
#
# 纪律：一律 `env -u LEAN_PATH lake build`；绝不 `lake update`（会拖新 mathlib）。
set -euo pipefail
cd "$(dirname "$0")"

# ── 真值来源：lake-manifest.json 的 rev（**层按 rev 选，不按目录名猜**）─────────
# 同一台机器上常并存多代检出（本机实测：v4.33.0-rc1 与 v4.34.0 正式 tag 各一份），
# 按目录名探测会落错层，而接错层时「目录在、标志物在」全都通过——只有 lake 发现 rev
# 不符，于是重新解析依赖（真的克隆一份，数小时）。故本脚本先按 rev
# 选层、再链接；收尾仍逐条对拍兜底（那一半对「候选全都不符」与「python 缺席」说话）。
MANIFEST=lake-manifest.json
PY=""
for c in python python3; do          # 顺序要紧：Windows 上 python3 常是应用商店
  if command -v "$c" >/dev/null 2>&1 && "$c" -c 'pass' >/dev/null 2>&1; then
    PY="$c"; break                   # 的占位别名，能解析到、但根本不执行脚本。
  fi
done
manifest_rev() {               # manifest_rev <包名> → 该包的 rev（取不到则空）
  if [ -f "$MANIFEST" ] && [ -n "$PY" ]; then
    "$PY" - "$MANIFEST" "$1" <<'PYEOF' || true
import json, sys
man = json.load(open(sys.argv[1], encoding="utf-8"))
for p in man["packages"]:
    if p["name"] == sys.argv[2]:
        print(p.get("rev", ""))
        break
PYEOF
  fi
  return 0
}
head_rev() {                   # head_rev <目录> → 该目录的 HEAD（非 git 检出则空）
  command -v git >/dev/null 2>&1 || { echo ""; return 0; }
  git -C "$1" rev-parse HEAD 2>/dev/null || echo ""
}
find_mathlib_in() {            # find_mathlib_in <根> → 该根下 rev 相符的检出（无则空）
  local want d
  want="$(manifest_rev mathlib)"
  [ -n "$want" ] || { echo ""; return 0; }
  for d in "$1/mathlib4" "$1"/*/; do
    d="${d%/}"
    [ -e "$d/.git" ] || continue
    [ "$(head_rev "$d")" = "$want" ] && { echo "$d"; return 0; }
  done
  echo ""
}

# ── 找全局根 ────────────────────────────────────────────────────────────────
GLOBAL="${LEAN_GLOBAL:-}"
if [ -z "$GLOBAL" ]; then
  for c in "$HOME/lean" "/c/lean" "C:/lean" "/opt/lean"; do
    [ -d "$c" ] || continue
    if [ -n "$(find_mathlib_in "$c")" ] || [ -d "$c/mathlib4" ]; then GLOBAL="$c"; break; fi
  done
fi
MATHLIB="${LEAN_DEPS_MATHLIB:-}"
if [ -z "$MATHLIB" ] && [ -n "$GLOBAL" ]; then
  MATHLIB="$(find_mathlib_in "$GLOBAL")"
  [ -n "$MATHLIB" ] || MATHLIB="$GLOBAL/mathlib4"   # 退到目录名探测；收尾对拍兜底
fi
PACKAGES="${LEAN_DEPS_PACKAGES:-${GLOBAL:-}/packages}"
LIBS="${LEAN_DEPS_LIBS:-${GLOBAL:-}/libs}"

if [ -z "$GLOBAL" ] || [ ! -d "$MATHLIB" ]; then
  echo "未找到全局 mathlib（试过 \$LEAN_GLOBAL、\$HOME/lean、/c/lean、C:/lean、/opt/lean）。"
  echo "直接运行 \`env -u LEAN_PATH lake build\`，由 lake 依 git 依赖自动取得依赖即可。"
  exit 0
fi
echo "全局根：$GLOBAL"
echo "  mathlib  ：$MATHLIB  (HEAD=$(head_rev "$MATHLIB" | cut -c1-12))"

# 依赖源：**同一层优先**——先在该 mathlib 检出自带的 `.lake/packages/`（本机
# $GLOBAL/packages 常常只放 LeanQEC/Physlib 这类下游库，8 个传递包其实在 mathlib
# 的检出里），再 $GLOBAL/packages、$GLOBAL/libs、$GLOBAL/vendor、$GLOBAL 根。
# 每个候选都与 manifest 的 rev 对一次：不符＝另一代检出，跳过并说明。
resolve() {                    # resolve <lake 包名> [目录别名…] → 回显可用的源目录
  local name="$1"; shift
  local want="" cand="" alias="" fallback=""
  want="$(manifest_rev "$name")"
  for alias in "$name" "$@"; do
    for cand in "$MATHLIB/.lake/packages/$alias" "$PACKAGES/$alias" \
                "$LIBS/$alias" "$GLOBAL/vendor/$alias" "$GLOBAL/$alias"; do
      [ -d "$cand" ] || continue
      if [ -z "$want" ] || [ "$(head_rev "$cand")" = "$want" ]; then
        echo "$cand"; return 0
      fi
      [ -n "$fallback" ] || fallback="$cand"
    done
  done
  echo "$fallback"             # 无相符者：退回第一个存在的候选，收尾对拍会点名
}
echo "  依赖源   ：同一层优先（$MATHLIB/.lake/packages → $PACKAGES → …，逐个对 rev）"

# ── 建链接（Windows 用目录联接，其余平台用符号链接）─────────────────────────
mkdir -p .lake/packages

unlink_safely() {              # 只摘掉链接本身，绝不递归进它指向的目标
  local p=".lake/packages/$1"
  [ -e "$p" ] || [ -L "$p" ] || return 0
  if [ -L "$p" ]; then
    rm -f "$p"                 # 普通符号链接：删链接即可，不递归
    return 0
  fi
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      # Windows 目录联接：必须用 rmdir 摘（`rm -rf` 会递归进目标，可能删掉
      # 全局共享 mathlib）。rmdir 对「真目录」会失败，那时才退回 rm -rf。
      cmd //c rmdir "$(cygpath -w "$PWD/$p")" >/dev/null 2>&1 ||
        rm -rf "$p" 2>/dev/null || true ;;
    *) rm -rf "$p" 2>/dev/null || true ;;
  esac
}

link() {                       # link <链接名> <目标>
  local name="$1" target="$2"
  [ -e "$target" ] || { echo "  跳过 $name（目标不存在：$target）"; return 0; }
  unlink_safely "$name"
  case "$(uname -s)" in
    MINGW*|MSYS*|CYGWIN*)
      # Windows：优先 PowerShell 的目录联接。MSYS 下 `cmd //c "mklink /J …"`
      # 会被路径转换破坏（报「文件、目录或卷标语法不正确」），故以 PowerShell
      # 为主路径、cmd 为退路；两者都失败时由末尾的校验统一报错。
      local win_target win_link
      win_target="$(cygpath -w "$target")"
      win_link="$(cygpath -w "$PWD/.lake/packages/$name")"
      powershell -NoProfile -Command \
        "New-Item -ItemType Junction -Path '$win_link' -Target '$win_target' | Out-Null" \
        >/dev/null 2>&1 ||
        cmd //c "mklink /J \"$win_link\" \"$win_target\"" >/dev/null 2>&1 || true ;;
    *)
      ln -sfn "$(cd "$target" && pwd)" ".lake/packages/$name" ;;
  esac
}

link mathlib "$MATHLIB"
for p in aesop batteries Cli importGraph LeanSearchClient plausible proofwidgets Qq; do
  src="$(resolve "$p")"
  if [ -n "$src" ]; then link "$p" "$src"; else echo "  跳过 $p（候选都缺）"; fi
done
link LeanQEC "$(resolve LeanQEC Lean-QEC)"
# QEC 走 QECLean 的 Gross 形式化（BB144 的内核内下界）。
link QEC "$(resolve QEC QECLean)"
# LeanArchitect：QECLean 的传递依赖。
link LeanArchitect "$(resolve LeanArchitect)"

# ── 校验 ────────────────────────────────────────────────────────────────────
# Windows 的目录联接在 readlink/`-type l` 下都表现为「真目录」，故不能靠 readlink
# 判空；改为检查链接**解析得到的目录里**是否存在该包的标志性子目录。
echo
echo "== 校验（各依赖的标志性入口是否可见）=="
missing=0
check() {                      # check <链接名> <目标内的标志物>
  if [ -e ".lake/packages/$1/$2" ]; then
    printf '  %-16s OK\n' "$1"
  else
    printf '  %-16s ✗ 未接上\n' "$1"; missing=1
  fi
}
check mathlib Mathlib
check aesop Aesop
check batteries Batteries
check Cli Cli
check importGraph ImportGraph
check LeanSearchClient LeanSearchClient
check plausible Plausible
check proofwidgets ProofWidgets
check Qq Qq
check LeanQEC LeanQEC
check QEC QEC
check LeanArchitect Architect

if [ "$missing" != "0" ]; then
  echo
  echo "✗ 有依赖没接上。可直接跳过本脚本：lake 会按 lakefile/lake-manifest 的 git 依赖"
  echo "  自己取（首次需联网，且 mathlib 若为全新克隆要跑一次全量编译）。"
  exit 1
fi

# ── 校验之二：每个链接的 HEAD 必须与 lake-manifest.json 的 rev 逐字相等 ──────
# 上面那一段只证明「接上了」，不证明「接对了层」。本脚本已按 rev 选层，但两种情形
# 仍会落错：候选全都不符（resolve 退回第一个存在的候选）与 python 缺席（退回目录名
# 探测）。而接错层时「目录在、标志物在」全都通过——只有 lake 发现 rev 不符，于是
# 重新解析依赖（真的克隆一份，数小时）。故收尾一律逐条对拍（实测判据：
# `git -C .lake/packages/<名> rev-parse HEAD` 逐条等于 manifest 的 rev）。
if [ -n "$PY" ] && [ -f lake-manifest.json ]; then
  echo
  echo "== rev 校验（链接的 HEAD 对 lake-manifest.json）=="
  set +e
  "$PY" - lake-manifest.json <<'PYEOF'
import json, os, subprocess, sys
man = json.load(open(sys.argv[1], encoding="utf-8"))
bad = 0
for p in man["packages"]:
    d = os.path.join(".lake", "packages", p["name"])
    if not os.path.isdir(d):
        continue
    r = subprocess.run(["git", "-C", d, "rev-parse", "HEAD"],
                       capture_output=True, text=True)
    head = r.stdout.strip()
    if head == p.get("rev"):
        print("  %-16s MATCH" % p["name"])
    elif not head:
        print("  %-16s 跳过（不是 git 检出，无法核对 rev）" % p["name"])
    else:
        print("  %-16s ✗ HEAD %s ≠ manifest %s"
              % (p["name"], head[:12], p.get("rev", "")[:12]))
        bad += 1
sys.exit(1 if bad else 0)
PYEOF
  rc=$?
  set -e
  if [ "$rc" != "0" ]; then
    echo
    echo "✗ 有链接接错了层：HEAD 与 manifest 的 rev 不符。lake 会据此重新解析依赖"
    echo "  （真的去克隆一份）。请把该链接改接到 rev 相符的那个检出再跑一次。"
    exit 1
  fi
else
  echo
  echo "（跳过 rev 校验：当前目录没有 lake-manifest.json，或找不到能执行的 python）"
fi

echo
echo "提醒：若 mathlib 是全新克隆（无预编译 olean），先在其目录跑 \`lake exe cache get\`"
echo "      再回来构建，可省下数小时的全量编译。"
