#!/usr/bin/env python3
# SPDX-License-Identifier: LGPL-3.0-or-later
# Copyright (c) 2026 Umang Mathur and contributors. See LICENSE and NOTICE.md.
"""Check local documentation links, build coverage, and Lean documentation examples."""

from pathlib import Path
import re
import subprocess
import tempfile
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


def check_links():
    documents = sorted(ROOT.glob("*.md")) + sorted((ROOT / "docs").glob("*.md"))
    count = 0
    for document in documents:
        text = re.sub(r"```.*?```", "", document.read_text(), flags=re.S)
        for target in re.findall(r"\]\(([^\s)]+)\)", text):
            url = urlsplit(target)
            if url.scheme or url.netloc or not url.path:
                continue
            path = (document.parent / unquote(url.path)).resolve()
            if not path.is_relative_to(ROOT) or not path.exists():
                raise SystemExit(f"Broken local link in {document.relative_to(ROOT)}: {target}")
            count += 1
    print(f"Checked {count} local documentation links.", flush=True)


def check_imports():
    sources = [ROOT / "RelationAlgebra.lean", *sorted((ROOT / "RelationAlgebra").rglob("*.lean"))]
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts): path for path in sources}
    reached = set()
    pending = ["RelationAlgebra"]
    while pending:
        module = pending.pop()
        if module in reached:
            continue
        if module not in modules:
            raise SystemExit(f"Missing local module: {module}")
        reached.add(module)
        imports = re.findall(r"^import\s+(RelationAlgebra(?:\.[\w]+)*)\s*$",
                             modules[module].read_text(), flags=re.M)
        pending.extend(imports)
    missing = modules.keys() - reached
    if missing:
        raise SystemExit("Modules outside the build/audit import closure: " + ", ".join(sorted(missing)))
    print(f"All {len(modules)} library modules are reachable from RelationAlgebra.", flush=True)


def check_lean_examples():
    total = 0
    with tempfile.TemporaryDirectory(prefix="relation-algebra-docs-") as temp:
        for document in [ROOT / "README.md", ROOT / "docs" / "GUIDE.md"]:
            blocks = re.findall(r"^```lean\s*\n(.*?)^```\s*$", document.read_text(), flags=re.M | re.S)
            if not blocks:
                raise SystemExit(f"No Lean examples found in {document.relative_to(ROOT)}")
            # Examples share the imports and scopes introduced earlier in their document.
            imports = ["import RelationAlgebra"]
            body = []
            for block in blocks:
                for line in block.splitlines():
                    if line.startswith("import "):
                        if line not in imports:
                            imports.append(line)
                    else:
                        body.append(line)
                body.append("")
            source = Path(temp) / f"{document.stem.title()}Examples.lean"
            source.write_text("\n".join(imports + [""] + body) + "\n")
            subprocess.run(["lake", "env", "lean", "-DwarningAsError=true", str(source)],
                           cwd=ROOT, check=True)
            total += len(blocks)
            print(f"Checked {len(blocks)} Lean examples in {document.relative_to(ROOT)}.", flush=True)
    print(f"All {total} documentation examples compile.", flush=True)


if __name__ == "__main__":
    check_links()
    check_imports()
    check_lean_examples()
