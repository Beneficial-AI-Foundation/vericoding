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
/* helper modified by LLM (iteration 5): fix spec fn parameter types for chord_intersects */
spec fn chord_intersects(chord1: &Vec<int>, chord2: &Vec<int>) -> bool {
    let a1 = if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] };
    let b1 = if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] };
    let a2 = if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] };
    let b2 = if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] };
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
}

spec fn chord_is_axis_aligned(chord: &Vec<int>, n: nat) -> bool {
    chord[0] != chord[1] && chord[0] >= 1 && chord[0] <= 2 * n && chord[1] >= 1 && chord[1] <= 2 * n
}

proof fn chord_intersection_symmetric(chord1: &Vec<int>, chord2: &Vec<int>) 
    ensures 
        chord_intersects(chord1, chord2) == chord_intersects(chord2, chord1)
{}

spec fn all_points_unique(chords: &Vec<Vec<int>>) -> bool {
    forall|i: int, j: int, k: int, l: int| 
        0 <= i < chords.len() && 0 <= j < chords.len() && 
        0 <= k < 2 && 0 <= l < 2 && 
        (i != j || k != l) ==> chords[i][k] != chords[j][l]
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
/* code modified by LLM (iteration 5): fix compilation errors by converting usize chords to int before checking intersection */
{
    let mut result = false;
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            let chord_i_as_int = Vec::<int>::new().push(chords[i][0] as int).push(chords[i][1] as int);
            let chord_j_as_int = Vec::<int>::new().push(chords[j][0] as int).push(chords[j][1] as int);
            proof {
                let intersects = chord_intersects(&chord_i_as_int, &chord_j_as_int);
                if intersects {
                    result = true;
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