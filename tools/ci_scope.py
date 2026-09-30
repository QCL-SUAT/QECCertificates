#!/usr/bin/env python3
"""CI scope: which modules a hosted runner can afford to build.

Why this exists: the library's memory-hungry modules are the ones that close a
statement by kernel reduction over a large object, and one of them peaks far above
what a hosted runner provides.  A continuous-integration job that builds the whole
library therefore dies at the tail, which teaches a reader nothing: a red badge
that means "the runner ran out of memory" is worse than an honest smaller scope.

The scope is the recorded measurement, not an opinion.  PEAK_MIB below holds, for
every module of the package, the peak working set of a compile of that module
alone, taken on the machine and date named above the table, on a quiet machine,
with the process sampled every few seconds.  A module whose peak exceeds
BUDGET_MIB is excluded, and so is every module that imports an excluded one,
transitively: lake cannot build a module without its dependencies, so the closure
is what a runner actually has to afford.  The table is meant to be maintained: a
new module is measured and recorded before it can be built anywhere.

Measuring one module, with nothing else of this project building:

    peak=0
    env -u LEAN_PATH lake env lean QECCertificates/<Layer>/<Module>.lean &
    job=$!
    while kill -0 $job 2>/dev/null; do
        m=$(powershell -NoProfile -Command "(Get-Process lean -ErrorAction \\
            SilentlyContinue | Measure-Object PeakWorkingSet64 -Maximum).Maximum")
        case "$m" in ''|*[!0-9]*) ;; *) [ "$m" -gt "$peak" ] && peak=$m ;; esac
        sleep 8
    done
    wait $job; echo $((peak/1048576)) MiB

On GNU/Linux the same number comes out of `/usr/bin/time -v lake env lean <file>`
as the maximum resident set size.  The sampler reads the peak of every lean
process on the machine, so a second build running at the same time inflates it.

Modes: --report (the table), --lake-targets (the CI command's argument list),
--check (fail when the tree and the table disagree), --self-test.

Exit: 0 = the scope is complete and consistent; 1 = the tree changed under it.
"""
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MODULE_DIR = "QECCertificates"
ROOT_MODULE = "QECCertificates.lean"

# A hosted runner provides 16 GB; the build process, the toolchain and the log
# leave room for about two thirds of that in a single module compile.
BUDGET_MIB = 10240

MEASURED = "2026-09-30"
MEASURED_ON = "Windows 11, 192-core host, 639 GB"   # the volume, not the runner

# module (path in the repository) -> peak working set of one compile, MiB
PEAK_MIB = {
    "QECCertificates.lean": 2980,
    "QECCertificates/Codes/BB144Distance.lean": 35221,
    "QECCertificates/Codes/BB144Literal.lean": 45386,
    "QECCertificates/Codes/BB144Rank.lean": 46648,
    "QECCertificates/Codes/BB144Symmetry.lean": 2965,
    "QECCertificates/Codes/BB144Witness.lean": 35327,
    "QECCertificates/Codes/BB18Anchor.lean": 8473,
    "QECCertificates/Codes/BB24Gauged.lean": 40829,
    "QECCertificates/Codes/BB24Separation.lean": 3218,
    "QECCertificates/Codes/BaconShor.lean": 11248,
    "QECCertificates/Codes/BaconShorMeasurement.lean": 3936,
    "QECCertificates/Codes/BoundaryCollapse.lean": 3207,
    "QECCertificates/Codes/CSSPair.lean": 3100,
    "QECCertificates/Codes/CaseMatrix.lean": 28062,
    "QECCertificates/Codes/DistanceLabel.lean": 2934,
    "QECCertificates/Codes/FoldTransversal.lean": 4956,
    "QECCertificates/Codes/FullProtocolFaults.lean": 18931,
    "QECCertificates/Codes/GaugeMeasurementInstance.lean": 5004,
    "QECCertificates/Codes/Gauging.lean": 3247,
    "QECCertificates/Codes/HGPToricFamily.lean": 29051,
    "QECCertificates/Codes/LPAnchor.lean": 8424,
    "QECCertificates/Codes/MeasurementProtocol.lean": 2947,
    "QECCertificates/Codes/Separation.lean": 2939,
    "QECCertificates/Codes/SeparationClosedForm.lean": 2935,
    "QECCertificates/Codes/SeparationInstances.lean": 78770,
    "QECCertificates/Codes/TimeLikeInstance.lean": 3693,
    "QECCertificates/Codes/ToricFamilySpatial.lean": 2945,
    "QECCertificates/GF2/Basic.lean": 3171,
    "QECCertificates/GF2/Canonical.lean": 2933,
    "QECCertificates/GF2/HGP.lean": 2936,
    "QECCertificates/GF2/HGPCleaning.lean": 3250,
    "QECCertificates/GF2/HGPCleaningDual.lean": 3181,
    "QECCertificates/GF2/HGPCompression.lean": 2930,
    "QECCertificates/GF2/HGPKunneth.lean": 3267,
    "QECCertificates/GF2/KernelBasis.lean": 3205,
    "QECCertificates/GF2/KunnethCore.lean": 3083,
    "QECCertificates/GF2/LiftedProduct.lean": 2927,
    "QECCertificates/GF2/LowerBound.lean": 3242,
    "QECCertificates/GF2/Membership.lean": 3173,
    "QECCertificates/GF2/RankCertificate.lean": 2919,
    "QECCertificates/GF2/RankEchelon.lean": 2923,
    "QECCertificates/GF2/RowReduce.lean": 2937,
    "QECCertificates/GF2/WeightEnum.lean": 2945,
    "QECCertificates/GF2/Witness.lean": 2946,
    "QECCertificates/Pauli/Expr.lean": 2943,
    "QECCertificates/Reflect/Certified.lean": 2949,
    "QECCertificates/Reflect/Complete.lean": 2938,
    "QECCertificates/Reflect/Encode.lean": 2943,
    "QECCertificates/Reflect/Faithful.lean": 2943,
    "QECCertificates/Reflect/FaithfulCircuit.lean": 3527,
    "QECCertificates/Reflect/LRAT.lean": 2932,
    "QECCertificates/Reflect/LRATData.lean": 38738,
    "QECCertificates/Reflect/LRATDataCircuit.lean": 5601,
    "QECCertificates/Reflect/LexLeader.lean": 3300,
    "QECCertificates/Reflect/SBAssembly.lean": 2971,
    "QECCertificates/Reflect/SymmetryBreak.lean": 2963,
}

IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)


def modules(root):
    """Every .lean file of the package, as repository-relative paths.

    `git ls-files <dir>` lists the directory recursively.  A glob such as
    `QECCertificates/**/*.lean` would skip a module sitting directly in that
    directory, which is precisely the file this gate must not lose.
    """
    out = subprocess.run(["git", "ls-files", MODULE_DIR], cwd=root,
                         capture_output=True, text=True)
    files = [p for p in out.stdout.split("\n") if p.endswith(".lean")]
    if os.path.isfile(os.path.join(root, ROOT_MODULE)):
        files.append(ROOT_MODULE)
    return sorted(files)


def module_name(path):
    """`QECCertificates/GF2/Basic.lean` -> `QECCertificates.GF2.Basic`."""
    return path[:-len(".lean")].replace("/", ".")


def imports_of(root, path):
    """The package-internal modules this file imports, as repository paths."""
    text = io.open(os.path.join(root, path), encoding="utf-8").read()
    known = {module_name(p): p for p in modules(root)}
    out = set()
    for name in IMPORT.findall(text):
        if name in known and known[name] != path:
            out.add(known[name])
    return out


def scope(root):
    """(covered, excluded, unrecorded) for the tree at `root`.

    `unrecorded` lists modules the table does not know about: the scope cannot be
    computed for them, and they are reported rather than silently assumed light.
    """
    mods = modules(root)
    unrecorded = [m for m in mods if m not in PEAK_MIB]
    graph = {m: imports_of(root, m) for m in mods}
    excluded = {m for m in mods if PEAK_MIB.get(m, 0) > BUDGET_MIB}
    grew = True
    while grew:
        grew = False
        for m in mods:
            if m not in excluded and graph[m] & excluded:
                excluded.add(m)
                grew = True
    covered = [m for m in mods if m not in excluded]
    return covered, sorted(excluded), unrecorded


def findings(root):
    """Problem strings; empty means the recorded scope matches the tree."""
    covered, excluded, unrecorded = scope(root)
    mods = set(modules(root))
    out = []
    for m in unrecorded:
        out.append("%s has no recorded peak -- measure it as the docstring "
                   "describes and record the line in PEAK_MIB" % m)
    for m in sorted(set(PEAK_MIB) - mods):
        out.append("PEAK_MIB names %s, which is not in the tree" % m)
    if not covered:
        out.append("the scope covers no module at all")
    return out, covered, excluded


def self_test():
    bad = 0
    tmp = tempfile.mkdtemp(prefix="ci_scope_")
    saved = dict(PEAK_MIB)
    try:
        os.makedirs(os.path.join(tmp, MODULE_DIR, "L"))

        def put(rel, text):
            io.open(os.path.join(tmp, rel), "w", encoding="utf-8",
                    newline="\n").write(text)

        # A imports B, B imports C (heavy); D stands alone (light)
        put(MODULE_DIR + "/A.lean", "import QECCertificates.L.B\n")
        put(MODULE_DIR + "/L/B.lean", "import QECCertificates.L.C\n")
        put(MODULE_DIR + "/L/C.lean", "theorem c : True := trivial\n")
        put(MODULE_DIR + "/L/D.lean", "theorem d : True := trivial\n")
        subprocess.run(["git", "init", "-q"], cwd=tmp, check=True)
        subprocess.run(["git", "add", "-A"], cwd=tmp, check=True,
                       capture_output=True)

        # control 1: everything recorded, C heavy -> only D is covered
        PEAK_MIB.clear()
        PEAK_MIB.update({MODULE_DIR + "/A.lean": 100, MODULE_DIR + "/L/B.lean": 100,
                         MODULE_DIR + "/L/C.lean": BUDGET_MIB + 1,
                         MODULE_DIR + "/L/D.lean": 100})
        problems, covered, excluded = findings(tmp)
        want = {MODULE_DIR + "/L/D.lean"}
        if problems or set(covered) != want:
            print("  x control 1: scope is %s, expected %s (%s)"
                  % (covered, sorted(want), problems), file=sys.stderr)
            bad = 1
        else:
            print("  ok control 1: the closure of a heavy module is excluded")

        # control 2: a module with no recorded peak -> reported, not assumed light
        PEAK_MIB.pop(MODULE_DIR + "/L/D.lean")
        problems, _covered, _ex = findings(tmp)
        if not any("no recorded peak" in m for m in problems):
            print("  x control 2: an unmeasured module was not reported: %s"
                  % problems, file=sys.stderr)
            bad = 1
        else:
            print("  ok control 2: an unmeasured module is reported")

        # control 3: a recorded module that left the tree -> reported
        PEAK_MIB[MODULE_DIR + "/L/Gone.lean"] = 1
        problems, _covered, _ex = findings(tmp)
        if not any("not in the tree" in m for m in problems):
            print("  x control 3: a stale table entry was not reported: %s"
                  % problems, file=sys.stderr)
            bad = 1
        else:
            print("  ok control 3: a stale table entry is reported")
    finally:
        PEAK_MIB.clear()
        PEAK_MIB.update(saved)
        shutil.rmtree(tmp, ignore_errors=True)
    return bad


def main():
    argv = sys.argv[1:]
    if "--self-test" in argv:
        print("CI scope, self-test:")
        return self_test()
    problems, covered, excluded = findings(ROOT_DIR)
    if "--lake-targets" in argv:
        for m in covered:
            print(module_name(m))
        return 1 if problems else 0
    if "--check" in argv:
        print("CI scope: %d of %d modules are built by continuous integration; "
              "%d are excluded" % (len(covered), len(covered) + len(excluded),
                                   len(excluded)))
        for m in problems:
            print("  x " + m)
        if problems:
            print("\nFAIL: the recorded scope no longer matches the tree.")
            return 1
        print("  ok every module of the package is accounted for")
        return 0
    print("CI scope, measured %s on %s; budget %d MiB" %
          (MEASURED, MEASURED_ON, BUDGET_MIB))
    for m in sorted(PEAK_MIB):
        mark = "excluded" if m in excluded else "in scope"
        print("  %6d MiB  %-12s %s" % (PEAK_MIB[m], mark, m))
    print("  %d in scope, %d excluded" % (len(covered), len(excluded)))
    for m in problems:
        print("  x " + m)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
