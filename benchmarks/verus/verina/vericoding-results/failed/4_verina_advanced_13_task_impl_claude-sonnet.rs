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
/* helper modified by LLM (iteration 5): removed type conversion in spec function call */
fn check_chord_intersection(chords: &Vec<Vec<usize>>, i: usize, j: usize) -> (result: bool)
    requires
        i < chords.len(),
        j < chords.len(),
        forall|k: int| 0 <= k < chords.len() ==> chords[k].len() == 2
    ensures
        result == (i != j && chord_intersects(&chords[i as int], &chords[j as int]))
{
    if i == j {
        false
    } else {
        let chord1 = &chords[i];
        let chord2 = &chords[j];
        let a1 = if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] };
        let b1 = if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] };
        let a2 = if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] };
        let b2 = if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] };
        (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
    }
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
    /* code modified by LLM (iteration 5): added decreases clause to while loops */
    let mut i = 0;
    while i < chords.len()
        invariant
            i <= chords.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < chords.len() && x != y ==> !chord_intersects(&chords[x], &chords[y])
        decreases chords.len() - i
    {
        let mut j = 0;
        while j < chords.len()
            invariant
                i < chords.len(),
                j <= chords.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < chords.len() && x != y ==> !chord_intersects(&chords[x], &chords[y]),
                forall|y: int| 0 <= y < j && i as int != y ==> !chord_intersects(&chords[i as int], &chords[y])
            decreases chords.len() - j
        {
            if check_chord_intersection(chords, i, j) {
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}