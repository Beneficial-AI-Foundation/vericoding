# Tasks that need fixing

## Non_compiling files (24)

Fix the following files in the `yaml` folder. They mostly involve moving definitions from `vc-preamble` to the front of `vc-theorems`.

- fvapps_good2.files.fvapps_000222
- fvapps_good2.files.fvapps_000445
- fvapps_good2.files.fvapps_000481
- fvapps_good2.files.fvapps_000855
- fvapps_good2.files.fvapps_001291
- fvapps_good2.files.fvapps_001384
- fvapps_good2.files.fvapps_001443
- fvapps_good2.files.fvapps_001663
- fvapps_good2.files.fvapps_001704
- fvapps_good2.files.fvapps_002012
- fvapps_good2.files.fvapps_002102
- fvapps_good2.files.fvapps_002405
- fvapps_good2.files.fvapps_002417
- fvapps_good2.files.fvapps_002823
- fvapps_good2.files.fvapps_002988
- fvapps_good2.files.fvapps_003029
- fvapps_good2.files.fvapps_003111
- fvapps_good2.files.fvapps_003223
- fvapps_good2.files.fvapps_003465
- fvapps_good2.files.fvapps_003734
- fvapps_good2.files.fvapps_003946
- fvapps_good2.files.fvapps_004362
- fvapps_good2.files.fvapps_004524
- fvapps_good2.files.fvapps_004589

## Unexpected sorries (16)

These tasks are in `poor/unexpected_sorry`. Happens when sorries occur within a code block rather than in isolation. Might need to fix the sorries with Claude Code, e.g. `decreasing_by sorry` can often be replaced by `decreasing_by all_goals simp_wf; omega`.

- fvapps_001157.lean: Unexpected prev_sig and result type impl with sorry type 3
- fvapps_001358.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_001699.lean: Unexpected prev_sig and result type impl with sorry type 3
- fvapps_001784.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_001984.lean: Unexpected prev_sig and result type impl with sorry type 3
- fvapps_002191.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_002209.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_002246.lean: Unexpected prev_cond with prev sorry type 2
- fvapps_002386.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_002932.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_003136.lean: Unexpected prev_sig with prev_sorry_type 2
- fvapps_003376.lean: Unexpected prev_sig with prev_sorry_type 2
- fvapps_003409.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_003761.lean: Unexpected prev_sig with prev_sorry_type 2
- fvapps_004086.lean: Unexpected prev_sig and result type impl with sorry type 2
- fvapps_004571.lean: Unexpected prev_sig and result type impl with sorry type 3

## Sorries in preamble (92)

The files in `poor/sorry_in_preamble` all have sorries in vc-preamble.




