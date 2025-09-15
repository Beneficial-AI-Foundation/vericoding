// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn chord_intersects(chord1: &Vec<usize>, chord2: &Vec<usize>) -> bool {
    let a1 = if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] };
    let b1 = if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] };
    let a2 = if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] };
    let b2 = if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] };
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper as it was not used and the original `chord_intersects` is sufficient */
// </vc-helpers>

// <vc-spec>
fn has_chord_intersection(n: usize, chords: &Vec<Vec<usize>>) -> (result: bool)
    requires
        n >= 2,
        chords.len() == n,
        forall|i: int| 0 <= i < chords.len() ==> (
            chords[i].len() == 2 &&
            chords[i][0] >= 1 && chords[i][0] <= 2 * n &&
            chords[i][1] >= 1 && chords[i][1] <= 2 * n
        ),

        forall|i: int, j: int, k: int, l: int| 
            0 <= i < chords.len() && 0 <= j < chords.len() && 
            0 <= k < 2 && 0 <= l < 2 && 
            (i != j || k != l) ==> chords[i][k] != chords[j][l],
    ensures
        result == exists|i: int, j: int| 
            0 <= i < chords.len() && 0 <= j < chords.len() && i != j &&
            #[trigger] chord_intersects(&chords[i], &chords[j]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed `j as int` in the invariant clause by adding a comma */
{
    let mut i: usize = 0;

    while i < chords.len()
        invariant
            0 <= i as int && i as int <= chords.len() as int,
            // All prior pairs (idx1, idx2) for idx1 < i have been checked and don't intersect.
            forall|idx1: int, idx2: int|
                0 <= idx1 < i as int && 0 <= idx2 < chords.len() as int && idx1 != idx2
                ==>
                !#[trigger] (chord_intersects(&chords[idx1 as usize], &chords[idx2 as usize])),
    {
        let mut j: usize = i + 1;
        while j < chords.len()
            invariant
                0 <= i as int && i as int < j as int, j as int <= chords.len() as int,
                // All pairs (idx1, idx2) with idx1 < i have been checked as non-intersecting.
                forall|idx1: int, idx2: int|
                    0 <= idx1 < i as int && 0 <= idx2 < chords.len() as int && idx1 != idx2
                    ==>
                    !#[trigger] (chord_intersects(&chords[idx1 as usize], &chords[idx2 as usize])),
                // All pairs (i, idx) with i < idx < j have been checked as non-intersecting.
                forall|idx: int|
                    i as int < idx && idx < j as int
                    ==>
                    !#[trigger] (chord_intersects(&chords[i as usize], &chords[idx as usize])),
        {
            if chord_intersects(&chords[i], &chords[j]) {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return !(exists|k: int, l: int| 0 <= k < chords.len() as int && 0 <= l < chords.len() as int && k != l && #[trigger] chord_intersects(&chords[k as usize], &chords[l as usize]));
}
// </vc-code>

}
fn main() {}