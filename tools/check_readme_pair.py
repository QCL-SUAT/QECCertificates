#!/usr/bin/env python3
r"""README pair gate: the English and Chinese READMEs stay in step.

Why this exists: a bilingual README is two files that drift the moment one side is
edited -- and drift here is silent, because each file reads perfectly on its own. The
repository shows the English one by default and links the Chinese one at the top; the
link is only worth having if the two say the same things, section for section.

What is checked, in both directions:
  * both files exist, and each links to the other (a reader who lands on either can
    switch);
  * the section headings agree -- same count, same order of positions, and the same
    table-of-contents length (titles differ by language; the shape must not);
  * the badge URLs agree as a set;
  * the command-line blocks agree **verbatim** (a command is not translated; if one
    side's build or verify snippet changes, this fails until the other follows);
  * the set of repository-relative link targets agrees (every file one side links, the
    other links too);
  * neither file carries a control character or a curly quote;
  * each file is clean of the whitespace a bilingual README collects by accident: no
    trailing spaces, no tabs, no non-breaking or ideographic spaces, no CRLF, no run of
    two spaces inside prose, and, on the Chinese side, no space between a Chinese
    character and the Latin, digits or code beside it, no half-width comma or full stop
    against one, and no half-width brackets wrapped around Chinese (`GF(2)线性代数` and a
    link's `](...)` followed by Chinese are both fine, so brackets are judged as a pair).
    Fenced code blocks are left alone -- they align their own columns, and `**77 GiB**`
    keeps the space it has because `ci_scope.py` reads that count with `\s+` and would
    stop matching a tightened one.

Exit 0 when the pair is in step, 1 otherwise. `--self-test` runs the positive and
negative controls on a temporary pair, so a run that only ever prints PASS is not the
only evidence.
"""
import io
import os
import re
import shutil
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
EN = "README.md"
ZH = "README.zh-CN.md"

HEAD = re.compile(r"^##\s+(.*)$", re.M)
BADGE = re.compile(r"https://(?:github\.com/[^)\s]*/badge\.svg|img\.shields\.io/[^)\s]+)")
FENCE = re.compile(r"```(\w*)\n(.*?)```", re.S)
LINK = re.compile(r"\[[^\]]+\]\(([^)#\s]+)\)")
CURLY = re.compile(r"[“”‘’]")


CJK = "一-鿿"
# whitespace that is not the ordinary space: non-breaking, the several narrow spaces,
# the ideographic space, and the byte-order mark that reads as one
ODD_WS = re.compile("[\u00a0\u2000-\u200a\u202f\u205f\u3000\ufeff]")   # not the ordinary space


def prose_segments(line):
    """The prose parts of one line, with Markdown structure stripped off.

    A heading, list item or table cell carries a separator space of its own
    (`## Title`, `* item`, `| cell |`), and that space is syntax, not prose -- so it
    is removed before the spacing rules run, or every well-formed file would fail.
    """
    body = re.sub(r"^\s*(?:#{1,6}\s+|[-*+]\s+|\d+\.\s+)", "", line)
    if line.lstrip().startswith("|"):
        cells = body.strip().strip("|").split("|")
        return [c for c in cells if set(c.strip()) - set("-: ")]
    return [body]


def spacing_findings(name, text):
    """Whitespace hygiene for one README; empty means clean.

    Both files go through the same rules, so the pair cannot drift in how it is
    typed.  A rule that names a Chinese character simply finds nothing in the
    English file -- which is the point of running it there too: a Chinese string
    landing in either file is checked the same way.
    """
    out = []
    if "\r" in text:
        out.append("%s 里有 CRLF；本仓一律 LF 行尾" % name)
    if text and not text.endswith("\n"):
        out.append("%s 末尾缺一个换行" % name)
    if re.search(r"\n{3,}", text):
        out.append("%s 里有连续空行" % name)
    in_fence = False
    for i, ln in enumerate(text.split("\n"), 1):
        if ln.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue                      # code blocks align their own columns
        if ln != ln.rstrip():
            out.append("%s:%d 行尾有多余空白" % (name, i))
        if "\t" in ln:
            out.append("%s:%d 含制表符" % (name, i))
        for ch in ODD_WS.findall(ln):
            out.append("%s:%d 含异常空白 U+%04X（应为普通空格）" % (name, i, ord(ch)))
        for seg in prose_segments(ln):
            m = re.search(r"\S {2,}\S", seg)
            if m:
                out.append("%s:%d 正文里有连续空格：%r" % (name, i, m.group(0)))
            for m in re.finditer("[%s] +\\S|\\S +[%s]" % (CJK, CJK), seg):
                out.append("%s:%d 中文与英文/数字/代码之间有多余空格：%r"
                           % (name, i, m.group(0)))
            # 半角的逗号句号一类紧贴中文就是事故。半角括号不能这样一刀切：`GF(2)线性代数`
            # 与 Markdown 链接的 `](...)` 后面紧跟中文都是合法的，故括号只看成对的那一对
            # ——括号**里**包着中文才算错。
            for m in re.finditer("[%s][,.;:!?]|[,.;:!?][%s]" % (CJK, CJK), seg):
                out.append("%s:%d 中文旁用了半角标点：%r" % (name, i, m.group(0)))
            for m in re.finditer(r"\(([^)]*)\)", seg):
                if re.search("[%s]" % CJK, m.group(1)):
                    out.append("%s:%d 半角括号里包着中文：%r" % (name, i, m.group(0)))
    return out


def read(path):
    with io.open(path, encoding="utf-8") as fh:
        return fh.read()


def findings(root):
    """Return a list of problem strings; empty means the pair is in step."""
    out = []
    en_p, zh_p = os.path.join(root, EN), os.path.join(root, ZH)
    for p in (en_p, zh_p):
        if not os.path.isfile(p):
            return ["%s 不存在" % os.path.basename(p)]
    en, zh = read(en_p), read(zh_p)

    # 1. cross links
    if "](%s)" % ZH not in en:
        out.append("English README 没有指向 %s 的链接（读者切不过去）" % ZH)
    if "](%s)" % EN not in zh:
        out.append("中文 README 没有指回 %s 的链接" % EN)

    # 2. headings: same count, same anchor positions, same TOC length
    eh, zh_h = HEAD.findall(en), HEAD.findall(zh)
    if len(eh) != len(zh_h):
        out.append("小节数不一致：英文 %d、中文 %d" % (len(eh), len(zh_h)))
    en_toc = len(re.findall(r"\]\(#[^)]*\)", en.split("\n## ", 1)[0]))
    zh_toc = len(re.findall(r"\]\(#[^)]*\)", zh.split("\n## ", 1)[0]))
    if en_toc != zh_toc:
        out.append("目录条数不一致：英文 %d、中文 %d" % (en_toc, zh_toc))

    # 3. badges
    eb, zb = set(BADGE.findall(en)), set(BADGE.findall(zh))
    if eb != zb:
        out.append("徽章不一致：英文独有 %s；中文独有 %s"
                   % (sorted(eb - zb), sorted(zb - eb)))

    # 4. command blocks: the commands verbatim, the trailing comments freely translated
    #    （命令不翻译；行尾注释是散文，允许译文——两者混在一起比会把正常翻译判成漂移）
    def commands(text):
        blocks = []
        for _lang, body in FENCE.findall(text):
            lines = []
            for ln in body.strip().split("\n"):
                cmd = ln.split("#", 1)[0].rstrip() if not ln.strip().startswith("#") else ""
                if cmd:
                    lines.append(cmd)
            blocks.append("\n".join(lines))
        return blocks

    ec, zc = commands(en), commands(zh)
    if ec != zc:
        out.append("命令行块不一致：英文 %d 块、中文 %d 块%s"
                   % (len(ec), len(zc), "" if len(ec) == len(zc) else "（条数就不同）"))
        for i, (a, b) in enumerate(zip(ec, zc)):
            if a != b:
                out.append("  第 %d 块不同：\n    英文 %r\n    中文 %r" % (i + 1, a, b))

    # 5. relative link targets
    def targets(text):
        # 互链本身按语言不同（英文页指中文页、反之亦然），由第 1 条单独判，故排除
        return {t for t in LINK.findall(text)
                if not t.startswith(("http://", "https://")) and t not in (EN, ZH)}

    et, zt = targets(en), targets(zh)
    if et != zt:
        out.append("仓库内链接目标不一致：英文独有 %s；中文独有 %s"
                   % (sorted(et - zt), sorted(zt - et)))
    for t in sorted(et & zt):
        if not os.path.exists(os.path.join(root, t)):
            out.append("链接目标在树里不存在：%s" % t)

    # 6. text hygiene
    for name, text in ((EN, en), (ZH, zh)):
        ctl = [hex(ord(c)) for c in text if ord(c) < 32 and c != "\n"]
        if ctl:
            out.append("%s 含控制字符 %s" % (name, ctl))
        if CURLY.search(text):
            out.append("%s 含弯引号" % name)

    # 7. 空格与排版：两版走同一套规则（原先这里是个什么都不做的占位）
    for name, text in ((EN, en), (ZH, zh)):
        out.extend(spacing_findings(name, text))
    return out


def self_test():
    bad = 0
    tmp = tempfile.mkdtemp(prefix="readme_pair_")
    try:
        def put(path, text):
            # 显式 UTF-8 + LF：本仓的可移植性门禁就查这个（它抓过本文件的前一版）
            io.open(path, "w", encoding="utf-8", newline="\n").write(text)

        def seed(d):
            put(os.path.join(d, "f.txt"), "x")

        def write(d, en, zh):
            put(os.path.join(d, EN), en)
            put(os.path.join(d, ZH), zh)

        # 对照 1（阳性基线）：一对同步的 README，必须通过
        d1 = os.path.join(tmp, "ok")
        os.makedirs(d1)
        seed(d1)
        write(d1,
              "# T\n\n[a](README.zh-CN.md)\n\n## One\n\n```bash\nlake build\n```\n\n## Two\n\n[f](f.txt)\n",
              "# T\n\n[a](README.md)\n\n## 一\n\n```bash\nlake build\n```\n\n## 二\n\n[f](f.txt)\n")
        if findings(d1):
            print("  ✗ 对照 1：同步的一对却报出问题：%s" % findings(d1), file=sys.stderr)
            bad = 1
        else:
            print("  ✓ 对照 1：同步的一对通过")

        # 对照 2：命令块被改了一侧 → 必须报
        d2 = os.path.join(tmp, "cmd")
        os.makedirs(d2)
        seed(d2)
        write(d2,
              "# T\n\n[a](README.zh-CN.md)\n\n## One\n\n```bash\nlake build\n```\n\n## Two\n\n[f](f.txt)\n",
              "# T\n\n[a](README.md)\n\n## 一\n\n```bash\nlake build --flag\n```\n\n## 二\n\n[f](f.txt)\n")
        if not any("命令行块不一致" in m for m in findings(d2)):
            print("  ✗ 对照 2：命令块的差异没被抓到", file=sys.stderr)
            bad = 1
        else:
            print("  ✓ 对照 2：命令块差异被抓到")

        # 对照 3：少一个小节 → 必须报
        d3 = os.path.join(tmp, "sec")
        os.makedirs(d3)
        seed(d3)
        write(d3,
              "# T\n\n[a](README.zh-CN.md)\n\n## One\n\n```bash\nlake build\n```\n\n## Two\n\n[f](f.txt)\n",
              "# T\n\n[a](README.md)\n\n## 一\n\n```bash\nlake build\n```\n")
        if not any("小节数不一致" in m for m in findings(d3)):
            print("  ✗ 对照 3：少一节没被抓到", file=sys.stderr)
            bad = 1
        else:
            print("  ✓ 对照 3：小节数差异被抓到")

        # 对照 4：互相切换的链接缺失 → 必须报
        d4 = os.path.join(tmp, "link")
        os.makedirs(d4)
        seed(d4)
        write(d4,
              "# T\n\n## One\n\n```bash\nlake build\n```\n\n## Two\n\n[f](f.txt)\n",
              "# T\n\n## 一\n\n```bash\nlake build\n```\n\n## 二\n\n[f](f.txt)\n")
        if not any("切不过去" in m or "指回" in m for m in findings(d4)):
            print("  ✗ 对照 4：缺互链没被抓到", file=sys.stderr)
            bad = 1
        else:
            print("  ✓ 对照 4：缺互链被抓到")

        # 对照 5-8（阳性）：空格与排版卫生，每类各植一处
        def spacing_case(tag, zh_body, want, start=61):
            d = os.path.join(tmp, tag)
            os.makedirs(d)
            seed(d)
            write(d,
                  "# T\n\n[a](README.zh-CN.md)\n\n## One\n\n```bash\nlake build\n```\n\n## Two\n\n[f](f.txt)\n",
                  "# T\n\n[a](README.md)\n\n## 一\n\n```bash\nlake build\n```\n\n## 二\n\n%s\n\n[f](f.txt)\n"
                  % zh_body)
            got = findings(d)
            if not any(want in m for m in got):
                print("  ✗ 对照 %s（%s）没被抓到（实得 %s）" % (start, tag, got), file=sys.stderr)
                return 1
            print("  ✓ 对照 %s：%s 被抓到" % (start, tag))
            return 0

        bad |= spacing_case("行尾空格", "文字 ", "行尾有多余空白", 5)
        bad |= spacing_case("正文连续空格", "文字   连着", "连续空格", 6)
        bad |= spacing_case("中英之间多余空格", "中文 words 混排", "中文与英文", 7)
        bad |= spacing_case("中文旁半角标点", "你好,世界", "半角标点", 8)

        # 对照 9（阴性，最要紧的一条）：**必须**放行的几种不能报——代码块里的对齐
        # 空格、`**77 GiB**` 里被 ci_scope.py 用 `\s+` 读的那个空格，以及 `GF(2)线性代数`
        # 与链接收尾 `](...)中文` 这种半角括号紧邻中文的合法写法（本轮真红过一次）。
        d9 = os.path.join(tmp, "exempt")
        os.makedirs(d9)
        seed(d9)
        write(d9,
              "# T\n\n[a](README.zh-CN.md)\n\n## One\n\n```bash\nlake build     # aligned comment\n```\n\n## Two\n\n[f](f.txt)\n",
              "# T\n\n[a](README.md)\n\n## 一\n\n```bash\nlake build     # 对齐注释\n```\n\n## 二\n\n峰值**77 GiB**。\n\nGF(2)线性代数，见[f](f.txt)与上面。\n")
        got9 = findings(d9)
        if got9:
            print("  ✗ 对照 9：放行项被误报：%s" % got9, file=sys.stderr)
            bad = 1
        else:
            print("  ✓ 对照 9：代码块对齐、`**77 GiB**` 的空格、半角括号紧邻中文均未被误报")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return bad


def main():
    if "--self-test" in sys.argv:
        print("README 对门禁的自检：")
        return self_test()
    print("README 对门禁：中英两版是否同步")
    problems = findings(ROOT)
    for m in problems:
        print("  ✗ " + m)
    if problems:
        print("\nREADME 对门禁：失败（见上）。")
        return 1
    print("  ✓ 两版同步：小节数一致、目录条数一致、徽章一致、命令行块逐字一致、"
          "仓库内链接目标一致、互链齐全、无控制字符与弯引号；"
          "两版都过同一套空格与排版检查（行尾、制表符、异常空白、CRLF、连续空行、"
          "正文连续空格、中英/中码之间、中文旁半角标点）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
