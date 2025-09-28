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
proof fn chord_ordering_helper(chord: &Vec<usize>) -> (usize, usize)
    ensures
        chord[0] != chord[1],
        let min_val = (if chord[0] < chord[1] { chord[0] } else { chord[1] }),
        let max_val = (if chord[0] > chord[1] { chord[0] } else { chord[1] }),
        result.0 == min_val,
        result.1 == max_val,
{
    /* helper modified by LLM (iteration 5): Fixed return type syntax */
    let min_val = if chord[0] < chord[1] { chord[0] } else { chord[1] };
    let max_val = if chord[0] > chord[1] { chord[0] } else { chord[1] };
    (min_val, max_val)
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
{
    /* code modified by LLM (iteration 5): Use helper function for chord ordering */
    let mut result = false;

    let mut i: usize = 0;
    while i < chords.len()
        invariant
            0 <= i <= chords.len(),
            !result == (
                forall|ii: int, jj: int| 
                    0 <= ii < i && 0 <= jj < chords.len() && ii != jj ==> 
                    !chord_intersects(&chords[ii], &chords[jj])
            )
        decreases chords.len() - i,
    {
        let mut j: usize = 0;
        while j < chords.len()
            invariant
                0 <= j <= chords.len(),
                !result == (
                    forall|jj: int| 0 <= jj < j && jj != i ==> 
                        !chord_intersects(&chords[i], &chords[jj])
                )
            decreases chords.len() - j,
        {
            if i != j {
                let chord_i = &chords[i];
                let chord_j = &chords[j];
                let (a1, b1) = chord_ordering_helper(chord_i);
                let (a2, b2) = chord_ordering_helper(chord_j);
                
                if (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1) {
                    result = true;
                    break;
                }
            }
            j += 1;
        }
        
        if result {
            break;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}