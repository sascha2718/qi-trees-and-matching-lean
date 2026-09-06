# Pending edits outside `lean/`

Edits the Lean cleanup requires in files outside `lean/`, which this pass did not touch
because another session is editing there. Each item names the file, the passage, and the
replacement. Delete an item once it is applied, and delete the file when it is empty.

## `CLAUDE.md`

- Line 41, the paragraph "All libraries must stay sorry-free and axiom-clean … Extend the
  relevant one when adding major results." The `AxCheck` modules no longer exist. Replace
  the sentences after "`propext, Classical.choice, Quot.sound` only." by: "The axiom audit
  is the comparator run: `lean/Challenge.lean` restates the headline theorems with `sorry`,
  `lean/Solution.lean` proves them from the libraries, and `lean/comparator-audit.sh` checks
  the pair (names in `lean/comparator-config.json`). Extend `Challenge.lean` and
  `Solution.lean` when adding major results."
- Line 73, the `GraphMarkovMatching` bullet: "`Archive/` for routes no longer referenced
  (correct and audited, built by `Archive.lean`)" is stale. Replace by: "`Archive/` for
  routes and declarations nothing live consumes, outside the default build and the public
  mirror, built by `lake build GraphMarkovMatching.Archive`; the other three libraries carry
  the same folder".
- Line 74, the `ChainClasses` bullet: "imports `GraphMatching` for the potential interface,
  while the first two libraries stay mutually independent". `EngineBridge.lean` imports
  `GraphMarkovMatching` as well. Replace by: "imports `GraphMatching` for the potential
  interface and `GraphMarkovMatching` for the composite two-law theorem
  (`EngineBridge`), while the first two libraries stay mutually independent".

## `appendices.tex`

- Lines 736–737: "Axiom cleanliness is checked in \leanname{lean/GraphMatching/AxCheck.lean},
  which runs \texttt{\#print axioms} on the thirty-five endpoints of this part." The file is
  gone. Replace by a sentence pointing at the comparator audit, for example: "Axiom
  cleanliness is checked by the comparator audit of \cref{<the section describing
  Challenge.lean and Solution.lean>}."
- Lines 1272–1273: the same sentence for \leanname{lean/ChainClasses/AxCheck.lean}; same
  replacement.
- Line 1860: "All five endpoints are covered by the axiom check \texttt{AxCheck.lean}."
  Replace by: "All five endpoints are covered by the comparator audit."

## `PAPER_PLAN.md`

- Line 960, item 9 "Lean hygiene": "`lake build` green, sorry-free and warning-free, every
  axiom check clean, `Archive/` still building." Replace by: "`lake build` green, sorry-free
  and warning-free, the comparator audit clean, the four archive umbrellas
  (`lake build GraphMarkovMatching.Archive ChainClasses.Archive BranchingProcess.Archive
  GraphMatching.Archive`) still building."

## `appendices.tex`, moved declarations

`GraphMarkovMatching/Tail/Block.lean` is now `GraphMarkovMatching/Composite/Resolvent.lean`
(same declarations). Three numeral lemmas moved from `Delta3/NumericClose` to
`Potential/Numerals`, and `Tlaw_map_restrictLab` moved from `Delta3/Infinite` to
`Closure/Infinite`.

- Line 1769, the file column of the `thm:renewal-weight-gap` row:
  "GraphMarkovMatching/Tail/Block, RenewalAlignment" → "GraphMarkovMatching/Composite/Resolvent,
  RenewalAlignment".
- Line 1870: "\leanname{Tail/Block.screened\_uniform\_bound\_functional}" →
  "\leanname{Composite/Resolvent.screened\_uniform\_bound\_functional}". The same sentence calls
  it "the axiom-checked declaration"; the comparator audit does not name it, so "the
  declaration" is the accurate wording.
- Lines 1921–1922, the `eq:numerals` rows: merge into one row,
  " \texttt{fourTwentySeventh\_K\_bound}, \texttt{chordConst\_five\_half\_le} &
  Potential/Numerals\\", and delete the `Delta3/NumericClose` continuation row.
- Line 2027, the file column of the `thm:marginal-consistency` row: "Delta3/Infinite" →
  "Closure/Infinite".
- Line 2134, the file list of the `rem:graded-seed-obstruction` row: "Tail/Block" →
  "Composite/Resolvent".

## `arbitrary_offspring_matching.tex`, commented `\leancomment` lines

Low priority: these lines are commented out.

- Line 541: "Delta3/NumericClose.two\_rpow\_five\_half\_le\_eight" →
  "Potential/Numerals.two\_rpow\_five\_half\_le\_eight".
- Line 3493: "Delta3/Infinite.Tlaw\_map\_restrictLab" → "Closure/Infinite.Tlaw\_map\_restrictLab".
- Line 4655: "Tail/Block.screened\_uniform\_bound\_functional" →
  "Composite/Resolvent.screened\_uniform\_bound\_functional".

## `appendices.tex`, file columns after the deduplication and the restructuring

The classification library now lives in folders (`Chain/`, `Scalar/`, `Shape/`, `Bushy/`,
`General/`, `Regime/`, `Engine/`, `Universality/`, `Classification/`); file names are
unchanged, so the bare file names in the ChainClasses tables stay valid. The rows below name
declarations that moved to a different file. Each item gives the row's line range and the
change to its file column.

- Lines 1566–1574 (`thm:relabel`): `markedQI\_relabel` and `relabel\_scale` are in
  `GeneralConstants`; replace "Relabel, Hairy, GeneralCoupling, GeneralShapeCoupling" by
  "Relabel, GeneralConstants, GeneralCoupling, GeneralShapeCoupling".
- Lines 1628–1635 (`thm:hairy-general`, identification): `gAssembly\_isometric\_sample` is in
  `SampleAssembly` and `skelToB\_isQIMap` in `CascadeEncoding`; replace "EngineBridge,
  BAssembly" by "EngineBridge, CascadeEncoding, SampleAssembly, BAssembly".
- Lines 1647–1652 (`thm:chain-separation`): `exists\_sphereFinset\_card` is in
  `StarGeometry`; replace "ChainSeparationProof, StarSeparation" by "ChainSeparationProof,
  StarGeometry, StarSeparation".
- Lines 1653–1658 (`thm:chain-general`, deterministic core): `PAssembly` and
  `isPortQI\_collapse` are in `Piece`, `blobAssembly\_isometric\_sample` and
  `blob\_flat\_glued` in `BlobPresented`; replace "BlobAssembly" by "Piece, BlobPresented,
  BlobAssembly".
- Lines 1659–1665 (`thm:hairy-general`): the four constants `general\_rate\_to\_one`,
  `relabel\_glued\_scale`, `cascade\_depth`, `cascade\_depth\_le` are in `GeneralConstants`;
  replace "Hairy, HairyGeneral" by "GeneralConstants, HairyGeneral".
- Lines 1759–1761 (`thm:qi-transitive`): `ae\_pair\_fst` and `ae\_pair\_outer` are in
  `Trichotomy`; replace "HairyCross" by "HairyCross, Trichotomy".
- Lines 1938–1939 (`thm:obstruction`): "Process/CrossedContext" → "Obstructions/CrossedContext".
- Lines 2060–2061 (`eq:composite-cardinals`): `cLetterBox\_card` is in `Composite/StepLetters`
  and `cRank\_eq` in `Composite/StepMatrices`; replace "Composite/Step" by
  "Composite/StepLetters, Composite/StepMatrices".
- The `Tail/Block` items above now read `Composite/Resolvent` (the module moved again, out of
  `Closure/`, with `RareMatrix`, `Green` and `ProductMeasure`, none of which the appendix
  names by path).

## `CLAUDE.md`, `PAPER_PLAN.md` and commented tex lines, after the module moves

- CLAUDE.md line 86: "`Process/CrossedContext.lean`'s `crossed_context_potential_top`" →
  "`Obstructions/CrossedContext.lean`'s `crossed_context_potential_top`".
- CLAUDE.md line 74, the `ChainClasses` bullet: optionally add "The modules are grouped in
  folders following the paper: `Chain/`, `Scalar/`, `Shape/`, `Bushy/`, `General/`,
  `Regime/`, `Engine/`, `Universality/`, with the public API in `Classification/`."
- PAPER_PLAN.md line 1448: "`Process/CrossedContext.crossed_context_potential_top`" →
  "`Obstructions/CrossedContext.crossed_context_potential_top`".
- arbitrary_offspring_matching.tex lines 1033, 1060, 1063 (commented `\leancomment`s):
  "Process/CrossedContext" → "Obstructions/CrossedContext".
