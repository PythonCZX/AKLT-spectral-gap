"""Assemble and audit the manuscript bibliography without network requests.

All source records are shipped in proofs/*references.bib and *refs.bib.
Duplicate records needed by independently compilable proof modules are
collapsed to a single canonical entry. Conflicting duplicates, unresolved
citation keys, or uncanonicalized aliases stop the generator explicitly.
This script does not run LaTeX or BibTeX.
"""
from collections import defaultdict
from pathlib import Path
import json
import re


PAPER = Path(__file__).resolve().parents[1]
ALIASES = {
    "ac:hormander1965": "Hormander1965",
    "q:LY2023": "LuciaYoung2023",
    "prob_abs2026": "AndreassonBermanSvensson2026",
    "geo_abs2026": "AndreassonBermanSvensson2026",
}


def blocks(text):
    """Read brace-delimited BibTeX entries, including nested title braces."""
    position = 0
    while True:
        match = re.search(r"(?m)^@(\w+)\s*\{([^,]+),", text[position:])
        if match is None:
            return
        start = position + match.start()
        opening = text.index("{", start)
        depth, end = 1, opening + 1
        while end < len(text) and depth:
            if text[end] == "{" and (end == 0 or text[end-1] != "\\"):
                depth += 1
            elif text[end] == "}" and (end == 0 or text[end-1] != "\\"):
                depth -= 1
            end += 1
        if depth:
            raise ValueError("Unbalanced BibTeX entry near " + text[start:start+60])
        yield text[start:end]
        position = end


def record(block):
    header = re.match(r"@(\w+)\s*\{([^,]+),", block)
    kind, key = header.groups()
    fields = {}
    position = header.end()
    while position < len(block)-1:
        match = re.search(r"(\w+)\s*=\s*\{", block[position:])
        if match is None:
            break
        name = match[1]
        opening = position + match.end()-1
        depth, end = 1, opening+1
        while end < len(block) and depth:
            if block[end] == "{" and block[end-1] != "\\":
                depth += 1
            elif block[end] == "}" and block[end-1] != "\\":
                depth -= 1
            end += 1
        if depth:
            raise ValueError(f"Unbalanced field {name} in {key}")
        fields[name.lower()] = re.sub(r"\s+", " ", block[opening+1:end-1]).strip()
        position = end
    return kind.lower(), key.strip(), fields


def cited_keys():
    citations = defaultdict(list)
    expression = re.compile(r"\\(?:[A-Za-z]*cite[A-Za-z]*|nocite)\*?(?:\s*\[[^\]]*\])*\s*\{([^}]+)\}")
    for path in sorted(PAPER.rglob("*.tex")):
        text = re.sub(r"(?m)(?<!\\)%.*$", "", path.read_text())
        for match in expression.finditer(text):
            for key in match[1].split(","):
                key = key.strip()
                if key != "*":
                    citations[key].append(str(path.relative_to(PAPER)))
    return dict(sorted(citations.items()))


def registry_citations():
    path = PAPER / "supplements" / "theorem_registry.json"
    if not path.exists():
        return []
    keys = set()
    def collect(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key == "bibliography_keys":
                    keys.update(item)
                else:
                    collect(item)
        elif isinstance(value, list):
            for item in value:
                collect(item)
    collect(json.loads(path.read_text()))
    return sorted(keys)


def normalized(field, value):
    if field == "doi":
        return re.sub(r"^https?://(?:dx\.)?doi\.org/", "", value.lower()).strip()
    if field == "eprint":
        return re.sub(r"v\d+$", "", value.lower().replace("arxiv:", ""))
    return re.sub(r"[^a-z0-9]", "", value.lower())


def main():
    paths = sorted(set((PAPER / "proofs").glob("*references.bib"))
                   | set((PAPER / "proofs").glob("*refs.bib")))
    entries, metadata, origins = {}, {}, defaultdict(list)
    duplicates = []
    for path in paths:
        for block in blocks(path.read_text()):
            kind, key, fields = record(block)
            if key in ALIASES:
                raise ValueError(f"Replace bibliography alias {key} by {ALIASES[key]} in {path}")
            origins[key].append(str(path.relative_to(PAPER)))
            if key in entries:
                if metadata[key] != (kind, fields):
                    raise ValueError(f"Conflicting duplicate bibliography record: {key}")
                duplicates.append(key)
                continue
            entries[key], metadata[key] = block, (kind, fields)
    identifier_collisions = {}
    for field in ("doi", "eprint", "title"):
        grouped = defaultdict(list)
        for key, (_, fields) in metadata.items():
            if fields.get(field):
                grouped[normalized(field, fields[field])].append(key)
        bad = {identifier: keys for identifier, keys in grouped.items() if len(keys) > 1}
        if bad:
            identifier_collisions[field] = bad
    if identifier_collisions:
        raise ValueError("Duplicate works require canonical keys: " + json.dumps(identifier_collisions))
    citations = cited_keys()
    registry_keys = registry_citations()
    missing = sorted((set(citations) | set(registry_keys))-set(entries))
    if missing:
        raise ValueError("Undefined citation keys: " + ", ".join(missing))
    text = "% Generated by code/build_bibliography.py from the included source records.\n\n"
    text += "\n\n".join(entries[key] for key in sorted(entries, key=str.casefold)) + "\n"
    target = PAPER / "references.bib"
    temporary = target.with_suffix(".bib.tmp")
    temporary.write_text(text)
    temporary.replace(target)
    report = {
        "status": "passed", "entries": len(entries), "unique_cited_keys": len(citations),
        "missing_citation_keys": missing, "duplicate_work_identifiers": identifier_collisions,
        "registry_citation_keys": registry_keys,
        "canonical_aliases": ALIASES, "identical_component_records_collapsed": duplicates,
        "uncited_entries": sorted(set(entries)-set(citations)),
        "sources": [str(path.relative_to(PAPER)) for path in paths],
        "record_origins": dict(sorted(origins.items())), "citation_locations": citations,
        "scope": "Citation-key and duplicate-work integrity. Primary-source metadata was checked separately; this offline generator does not claim a fresh network audit.",
    }
    output = PAPER / "build" / "bibliography_audit.json"
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("status", "entries", "unique_cited_keys", "missing_citation_keys", "identical_component_records_collapsed")}, indent=2))


if __name__ == "__main__":
    main()
