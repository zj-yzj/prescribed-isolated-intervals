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
4. Confirm that the manuscript refers to Nathanson's public
   `arXiv:2605.26425v3` numbering, where the relevant multi-interval questions
   are Problems 14 and 15.

To generate a local upload bundle:

```powershell
Compress-Archive -LiteralPath arxiv\main.tex -DestinationPath arxiv\prescribed-isolated-intervals-arxiv-v1.zip -Force
tar -tf arxiv\prescribed-isolated-intervals-arxiv-v1.zip
```

The zip should list exactly `main.tex`. The generated zip is ignored by Git
because it is a local upload artifact.
