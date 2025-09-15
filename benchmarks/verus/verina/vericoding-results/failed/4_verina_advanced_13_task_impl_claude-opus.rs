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
{
    /* code modified by LLM (iteration 5): fixed syntax error with sequence length access */
    let n_chords = chords.len();
    for i in 0..n_chords
        invariant
            forall|a: int, b: int| 0 <= a < i as int && 0 <= b < n_chords as int && a != b ==> !chord_intersects(&chords[a], &chords[b])
    {
        for j in 0..n_chords
            invariant
                forall|a: int, b: int| 0 <= a < i as int && 0 <= b < n_chords as int && a != b ==> !chord_intersects(&chords[a], &chords[b]),
                forall|b: int| 0 <= b < j as int && i as int != b ==> !chord_intersects(&chords[i as int], &chords[b])
        {
            if i != j {
                assert(0 <= i as int);
                assert(i as int < chords@.len() as int);
                assert(0 <= j as int);
                assert(j as int < chords@.len() as int);
                let chord1 = &chords[i];
                let chord2 = &chords[j];
                
                let a1 = if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] };
                let b1 = if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] };
                let a2 = if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] };
                let b2 = if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] };
                
                if (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1) {
                    assert(chord_intersects(&chords[i as int], &chords[j as int]));
                    return true;
                }
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}