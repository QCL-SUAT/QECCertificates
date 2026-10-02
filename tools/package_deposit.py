#!/usr/bin/env python3
r"""Package a tagged tree as the Zenodo deposit archive.

Why this exists: the deposit is an archive of the source tree as tagged, and an
archive made by hand from a working tree carries whatever the machine happened
to have in it -- build artefacts, local notes, a paper PDF that is or is not the
compiled one.  `git archive` reads the committed tree of a revision instead, so
the deposit is the tree the tag names and nothing else.

The layout follows the deposit of v0.1.0 (record 10.5281/zenodo.23056680): a
zip whose single top-level directory is `QECCertificates-v<version>/`, holding
the tracked files of the tagged tree.  The version is read from the tagged
tree's own CITATION.cff, and when the revision is a tag whose name is
`v<version>`, the two must agree: v0.1.1 shipped with a CITATION.cff that still
said 0.1.0, and a deposit packaged from it would have been named for a version
the metadata inside it did not carry.  A mismatch is refused here rather than
packaged.

Writes `dist/QECCertificates-v<version>.zip` and a `.sha256` beside it.  `dist/`
is not tracked: the archive is regenerated from the tag whenever it is needed.
"""

import argparse
import hashlib
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def git(args: list) -> str:
    """Run git in the repository and return stdout, failing loudly."""
    out = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, encoding="utf-8"
    )
    if out.returncode != 0:
        sys.exit(f"git {' '.join(args)} failed:\n{out.stderr.strip()}")
    return out.stdout


def version_of(ref: str) -> str:
    """Read `version:` from the tagged tree's own CITATION.cff."""
    cff = git(["show", f"{ref}:CITATION.cff"])
    match = re.search(r'^version:\s*"([^"]+)"', cff, flags=re.M)
    if match is None:
        sys.exit(f"no `version:` field in {ref}:CITATION.cff")
    return match.group(1)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "ref", nargs="?", default="HEAD", help="revision to package (default: HEAD)"
    )
    args = parser.parse_args()

    ref = args.ref
    version = version_of(ref)

    resolved = git(["rev-parse", "--verify", "--quiet", f"{ref}^{{}}"]).strip()
    tag_name = git(["tag", "--points-at", resolved]).strip().splitlines()
    if tag_name and tag_name[0] != f"v{version}":
        sys.exit(
            f"ref {ref} is tag {tag_name[0]}, but its CITATION.cff says version "
            f"{version}; bump CITATION.cff or fix the tag before packaging"
        )

    prefix = f"QECCertificates-v{version}/"
    out_dir = ROOT / "dist"
    out_dir.mkdir(exist_ok=True)
    out_path = out_dir / f"QECCertificates-v{version}.zip"

    subprocess.run(
        ["git", "archive", "--format=zip", f"--prefix={prefix}",
         "-o", str(out_path), ref],
        cwd=ROOT, check=True,
    )

    digest = hashlib.sha256(out_path.read_bytes()).hexdigest()
    sum_path = out_path.with_suffix(".zip.sha256")
    with open(sum_path, "w", encoding="utf-8", newline="\n") as handle:
        handle.write(f"{digest}  {out_path.name}\n")

    size = out_path.stat().st_size
    print(f"packaged {ref} as {out_path.relative_to(ROOT)} ({size} bytes)")
    print(f"sha256 {digest}")


if __name__ == "__main__":
    main()
