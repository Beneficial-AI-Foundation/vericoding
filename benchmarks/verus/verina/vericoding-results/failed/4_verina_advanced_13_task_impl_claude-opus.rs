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
    /* code modified by LLM (iteration 5): Fixed syntax error in invariant quantifier */
    let mut i = 0;
    while i < chords.len()
        invariant
            0 <= i <= chords.len(),
            chords.len() == n,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < chords.len() && k != l ==> !chord_intersects(&chords[k], &chords[l]),
    {
        let mut j = i + 1;
        while j < chords.len()
            invariant
                i < j <= chords.len(),
                i < chords.len(),
                chords.len() == n,
                forall|k: int, l: int| 0 <= k < i && 0 <= l < chords.len() && k != l ==> !chord_intersects(&chords[k], &chords[l]),
                forall|l: int| i as int < l && l < j as int ==> !chord_intersects(&chords[i as int], &chords[l as int]),
        {
            let a1 = if chords[i][0] < chords[i][1] { chords[i][0] } else { chords[i][1] };
            let b1 = if chords[i][0] > chords[i][1] { chords[i][0] } else { chords[i][1] };
            let a2 = if chords[j][0] < chords[j][1] { chords[j][0] } else { chords[j][1] };
            let b2 = if chords[j][0] > chords[j][1] { chords[j][0] } else { chords[j][1] };
            
            if (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1) {
                assert(chord_intersects(&chords[i as int], &chords[j as int]));
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}