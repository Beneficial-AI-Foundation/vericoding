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
/* helper modified by LLM (iteration 5): symmetry of chord_intersects */
spec fn chord_intersects_sym(ch1: &Vec<usize>, ch2: &Vec<usize>) -> bool { chord_intersects(ch1, ch2) == chord_intersects(ch2, ch1) }

/* helper modified by LLM (iteration 5): convert vector length to int */
spec fn vec_len_int<T>(v: &Vec<T>) -> int { v.len() as int }
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
    /* code modified by LLM (iteration 5): iterative search with corrected invariant syntax avoiding `@` */
    let len = chords.len() as int;
    let mut i: int = 0;
    while i < len
        invariant 0 <= i && i <= len
        invariant (forall |p: int, q: int| (0 <= p && p < i && p < q && q < len) ==> !chord_intersects(&chords[p as usize], &chords[q as usize]))
        decreases len - i
    {
        let mut j: int = i + 1;
        while j < len
            invariant i + 1 <= j && j <= len
            invariant (forall |q: int| (i < q && q < j) ==> !chord_intersects(&chords[i as usize], &chords[q as usize]))
            decreases len - j
        {
            if chord_intersects(&chords[i as usize], &chords[j as usize]) {
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