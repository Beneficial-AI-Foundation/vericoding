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
/* helper modified by LLM (iteration 4): Removed unused helpers */
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
/* code modified by LLM (iteration 4): Fixed assert forall syntax by adding 'by' keyword. */
{
    let num_chords = chords.len();

    if num_chords < 2 {
        return false;
    }

    let mut i = 0;
    while i < num_chords
        invariant
            i <= num_chords,
            num_chords == chords.len(),
            forall|idx: int| 0 <= idx < num_chords ==> (
                chords[idx].len() == 2 &&
                chords[idx][0] >= 1 && chords[idx][0] <= 2 * n &&
                chords[idx][1] >= 1 && chords[idx][1] <= 2 * n
            )
        decreases num_chords - i
    {
        let mut j = i + 1;
        while j < num_chords
            invariant
                i < num_chords,
                j <= num_chords,
                num_chords == chords.len(),
                forall|idx: int| 0 <= idx < num_chords ==> (
                    chords[idx].len() == 2 &&
                    chords[idx][0] >= 1 && chords[idx][0] <= 2 * n &&
                    chords[idx][1] >= 1 && chords[idx][1] <= 2 * n
                )
            decreases num_chords - j
        {
            let chord1 = &chords[i];
            let chord2 = &chords[j];

            let a1 = if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] };
            let b1 = if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] };
            let a2 = if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] };
            let b2 = if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] };

            if (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1) {
                proof {
                    assert(chord_intersects(chord1, chord2));
                    assert(exists|x: int, y: int| 0 <= x < chords.len() && 0 <= y < chords.len() && x != y && chord_intersects(&chords[x], &chords[y]));
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assert forall|x: int, y: int| !(0 <= x < chords.len() && 0 <= y < chords.len() && x != y && chord_intersects(&chords[x], &chords[y]))
        implies
        !exists|x: int, y: int| 0 <= x < chords.len() && 0 <= y < chords.len() && x != y && chord_intersects(&chords[x], &chords[y]) by {};
    }
    false
}
// </vc-code>

}
fn main() {}