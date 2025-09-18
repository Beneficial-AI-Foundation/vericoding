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
/* helper modified by LLM (iteration 5): Removed unnecessary proof body as Verus can deduce from definition */
proof fn chord_intersects_symmetric(c1: &Vec<usize>, c2: &Vec<usize>)
    requires
        c1.len() == 2,
        c2.len() == 2,
    ensures
        chord_intersects(c1, c2) == chord_intersects(c2, c1),
{
}
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
/* code modified by LLM (iteration 5): Changed the invariant condition from `i as int + 1 <= j as int` to `i as int < j as int` to fix a compilation error related to comma parsing. The condition `i < j` is still implied through the outer loop for `i` and inner loop for `j` which starts at `i + 1`. */
{
    let n_idx = n as int;
    let chords_len = chords.len() as int;

    let mut i: usize = 0;
    while (i as int) < chords_len
        invariant
            0 <= i as int,
            i as int <= chords_len,
            chords.len() == n_idx,
            forall|k: int| 0 <= k < chords.len() ==> (
                chords[k].len() == 2 &&
                chords[k][0] >= 1 && chords[k][0] <= 2 * n_idx &&
                chords[k][1] >= 1 && chords[k][1] <= 2 * n_idx
            ),
            forall|p: int, q: int, r: int, s: int|
                0 <= p < chords.len() && 0 <= q < chords.len() &&
                0 <= r < 2 && 0 <= s < 2 &&
                (p != q || r != s) ==> chords[p][r] != chords[q][s],
    {
        let mut j: usize = i + 1;
        while (j as int) < chords_len
            invariant
                0 <= i as int,
                i as int < chords.len(),
                i as int < j as int, // This implies i < j
                j as int <= chords_len,
                chords.len() == n_idx,
                forall|k: int| 0 <= k < chords.len() ==> (
                    chords[k].len() == 2 &&
                    chords[k][0] >= 1 && chords[k][0] <= 2 * n_idx &&
                    chords[k][1] >= 1 && chords[k][1] <= 2 * n_idx
                ),
                forall|p: int, q: int, r: int, s: int|
                    0 <= p < chords.len() && 0 <= q < chords.len() &&
                    0 <= r < 2 && 0 <= s < 2 &&
                    (p != q || r != s) ==> chords[p][r] != chords[q][s],
        {
            assert(i as int != j as int);
            if chord_intersects(&chords[i], &chords[j])
            {
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}