# The logo

The mark is a ring of five qubits around a checkmark: a code, and a certificate for it.
The ring is the five-qubit code; the check is the thing this library exists to attach to a
parameter -- an UNSAT verdict that a third party can re-derive, a distance with a proof.
Flat shapes only, three colours, so it stays legible at the size GitHub shows.

| File | What it is |
|---|---|
| `qeccertificates-logo.svg` | the source, drawn in a 512-unit square, rendered at 128 px wherever its own size is used |
| `qeccertificates-logo-512.png` | raster for uploads that want a raster (GitHub org avatar, social previews) |
| `qeccertificates-logo-256.png` | the same, at 256 |
| `qeccertificates-logo-128.png` | the same, at 128 |
| `qeccertificates-logo-64.png` | the same, at 64 |
| `qeccertificates-logo-32.png` | the same, at 32 |

The SVG is the source of truth; the PNGs are renders. Re-render after editing the source
(with [Inkscape](https://inkscape.org/) on `PATH`, run from the repository root):

```bash
for s in 512 256 128 64 32; do
  inkscape assets/logo/qeccertificates-logo.svg \
    --export-filename=assets/logo/qeccertificates-logo-${s}.png \
    --export-width=$s --export-height=$s
done
```

Both `README.md` and `README.zh-CN.md` show the SVG under the title. GitHub shows the
**organization** avatar to the left of a repository name and does not take a
per-repository image, so the repository's own branding lives in the README, on the
repository page, and the 512 render is what to upload where a raster is wanted.

The files here carry the repository's license, Apache-2.0; see `LICENSE` and `NOTICE`.
