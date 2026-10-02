#!/usr/bin/env python3
"""Flag text in the article that repeats, word for word, a paper it cites.

Usage:  python3 tools/originality_check.py [N]      (default N = 5)

Downloads the cited papers that are on arXiv (into a temporary directory; nothing
is stored in the repository), extracts their text with `pdftotext`, and lists
every run of N or more consecutive words that appears both in them and in the
prose of paper/main.tex or paper/supplement.tex. Bibliographies, mathematics,
figures and authors' names are ignored, so what remains is prose.

A hit is not necessarily a problem: technical terms ("convex equilateral small
polygons") and URLs recur in every paper of the field. Every hit must be read,
and any sentence that repeats a cited paper must be rewritten. It found, in
2026-10, the second sentence of the abstract copied from Bingane and Audet's
abstract, and four stock phrases of their papers.

Papers that are not on arXiv (Reinhardt, Vincze, Datta, Tamvakis, Audet-Hansen-
Messine, Mossinghoff's journal papers) cannot be checked this way.
"""
import os, re, subprocess, sys, tempfile, urllib.request

ROOT = os.path.normpath(os.path.join(os.path.dirname(__file__), ".."))
ARXIV = {  # cited, or by the same authors on the same problem
    "2105.10618": "Bingane-Audet, maximal perimeter of equilateral small polygons",
    "2110.00036": "Bingane-Audet, equilateral small octagon of maximal width",
    "2110.11741": "Bingane, maximal area of small polygons (DCG)",
    "2608.08001": "Guo-Luo, Reinhardt's problem for n = 16, 32, 64",
    "2010.02490": "Bingane, perimeter and width of convex small polygons",
    "2106.11831": "Bingane, maximal perimeter and width",
    "2204.04547": "Bingane-Mossinghoff, small polygons with large area",
    "2009.07893": "Bingane, largest small polygons",
}
NAMES = {"audet", "hansen", "messine", "perron", "bingane", "mossinghoff", "reinhardt",
         "vincze", "datta", "tamvakis", "guo", "luo", "hare"}


def tex_words(s):
    if r"\begin{thebibliography}" in s:
        s = s[:s.index(r"\begin{thebibliography}")]
    s = re.sub(r"%.*", "", s)
    s = re.sub(r"\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}", " ", s, flags=re.S)
    s = re.sub(r"\\\(.*?\\\)", " ", s, flags=re.S)
    s = re.sub(r"\\\[.*?\\\]", " ", s, flags=re.S)
    s = re.sub(r"\\begin\{(equation|tabular|gather|align)\*?\}.*?\\end\{\1\*?\}", " ", s, flags=re.S)
    s = re.sub(r"\\[a-zA-Z]+\*?(\[[^\]]*\])?", " ", s)
    s = re.sub(r"[{}~$]", " ", s)
    return re.findall(r"[a-zA-Z][a-zA-Z'-]*", s.lower())


def pdf_words(path):
    t = subprocess.run(["pdftotext", "-q", path, "-"], capture_output=True, text=True).stdout
    t = re.sub(r"-\n", "", t)
    k = t.rfind("References")
    return re.findall(r"[a-zA-Z][a-zA-Z'-]*", (t[:k] if k > 0 else t).lower())


def main(n):
    ours = {f: tex_words(open(os.path.join(ROOT, "paper", f)).read())
            for f in ("main.tex", "supplement.tex") if os.path.exists(os.path.join(ROOT, "paper", f))}
    if not ours:
        sys.exit("paper/main.tex not found")
    hits = 0
    with tempfile.TemporaryDirectory() as tmp:
        for aid, label in ARXIV.items():
            pdf = os.path.join(tmp, aid + ".pdf")
            req = urllib.request.Request(f"https://arxiv.org/pdf/{aid}", headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=60) as r, open(pdf, "wb") as f:
                f.write(r.read())
            ref = pdf_words(pdf)
            grams = {tuple(ref[i:i + n]) for i in range(len(ref) - n + 1)}
            for name, words in ours.items():
                i = 0
                while i < len(words) - n + 1:
                    if tuple(words[i:i + n]) in grams:
                        j = i + n
                        while j < len(words) and tuple(words[j - n + 1:j + 1]) in grams:
                            j += 1
                        if not set(words[i:j]) & NAMES:
                            hits += 1
                            print(f"{name:15s} arXiv:{aid} ({label})\n    [{j - i} words] {' '.join(words[i:j])}")
                        i = j
                    else:
                        i += 1
    print(f"\n{hits} shared runs of {n}+ words. Read each one; rewrite any sentence that repeats a cited paper.")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
