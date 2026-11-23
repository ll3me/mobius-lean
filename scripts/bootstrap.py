"""Fetch the pinned, core-only Cook–Levin dependency. Optionally install a
verified Apple Silicon Lean distribution inside this project only."""
import argparse
import hashlib
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REVISION = "3e603e795b44fedcf7d6dd65b7d1e30547ead925"
SOURCE_HASH = "1c0f46a8ccc32a190cf74266fa0ab81ed91263b7b7d2155cedfe677b7d614230"
VERSION = "4.35.0-rc2"
MAC_HASH = "e721cf30671d3830fa6120c7b1a4e6b22624650ce1d618c0ca28a4889f5ef324"


def install(dest, url, digest, marker, compressed_zstd=False, bundled=None):
    stamp = dest / ".source-revision"
    if stamp.is_file() and stamp.read_text().strip() == marker:
        return
    if dest.exists():
        raise SystemExit(f"Existing directory has no matching source stamp: {dest}")
    dest.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=dest.parent) as tmp:
        archive = Path(tmp) / "download"
        if bundled is not None and bundled.is_file():
            shutil.copyfile(bundled, archive)
        else:
            subprocess.run(["curl","--fail","--location","--retry","2","--output",str(archive),url],check=True)
        h = hashlib.sha256()
        with archive.open("rb") as file:
            for chunk in iter(lambda: file.read(1 << 20), b""):
                h.update(chunk)
        if h.hexdigest() != digest:
            raise SystemExit(f"Archive checksum mismatch for {url}")
        tree = Path(tmp) / "tree"
        tree.mkdir()
        args = ["tar","--zstd","-xf"] if compressed_zstd else ["tar","-xzf"]
        subprocess.run([*args,str(archive),"--strip-components=1","-C",str(tree)],check=True)
        (tree / stamp.name).write_text(marker + "\n")
        os.rename(tree,dest)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local-lean",action="store_true",help="also install the pinned Apple Silicon compiler under .toolchain")
    args = parser.parse_args()
    install(ROOT/".deps"/"npcomplete",
            f"https://codeload.github.com/RBarish-UTokyo/NPCompleteness-Lean4/tar.gz/{REVISION}",
            SOURCE_HASH, REVISION, bundled=ROOT/"vendor"/"npcomplete-3e603e79.tar.gz")
    if args.local_lean:
        if platform.system() != "Darwin" or platform.machine() != "arm64":
            raise SystemExit("Use elan with the supplied lean-toolchain on this platform.")
        install(ROOT/".toolchain",
                f"https://github.com/leanprover/lean4/releases/download/v{VERSION}/lean-{VERSION}-darwin_aarch64.tar.zst",
                MAC_HASH, VERSION, compressed_zstd=True)

