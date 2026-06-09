# arXiv submission source

Upload `main.tex` as the TeX source for the first arXiv version. The paper is
self-contained and does not require figures, a `.bib` file, or auxiliary data.

Suggested metadata:

- Title: `Prescribed Isolated Intervals in Higher Fold Sumsets`
- Author: `Zijie Yu`
- Category: `math.NT`
- Comments: `16 pages; includes computational and Lean 4 verification notes`

Recommended license choice for a first posting where the author wants to keep
ordinary copyright control: `arXiv.org perpetual, non-exclusive license`.

Before upload:

1. Confirm that `paper/prescribed-isolated-intervals.pdf` was generated from
   the current `arxiv/main.tex`.
2. Run `python -m pytest` and `lake build`.
3. Check the TeX log for unresolved references or overfull boxes.
4. If Nathanson's public arXiv version has not yet caught up with the
   June 8 draft revision, keep the paper's wording as `June 8, 2026 draft
   revision`.
