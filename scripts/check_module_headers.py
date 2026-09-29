#!/usr/bin/env python3
"""Check Palomar module headers in tracked Lean sources, excluding local archives."""

from pathlib import Path
import subprocess
import sys


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    paths = subprocess.check_output(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=root
    ).decode("utf-8").split("\0")
    sources = [path for path in paths if path]
    failures = []
    for source in sources:
        try:
            lines = (root / source).read_text(encoding="utf-8").lstrip().splitlines()
            if not lines or lines[0].strip() != "module":
                failures.append(f"{source}: must begin with `module` on its own line")
        except (OSError, UnicodeError) as error:
            failures.append(f"{source}: {error}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    if not sources:
        print("No tracked Lean sources found", file=sys.stderr)
        return 1
    print(f"Module headers checked: {len(sources)} tracked Lean sources")
    return 0


if __name__ == "__main__":
    sys.exit(main())
