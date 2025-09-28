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
/* helper modified by LLM (iteration 2): [no code changes, just added comment] */
proof fn lemma_chord_intersects_is_symmetric(chord1: &Vec<usize>, chord2: &Vec<usize>)
    requires
        chord1.len() == 2,
        chord2.len() == 2,
    ensures
        chord_intersects(chord1, chord2) == chord_intersects(chord2, chord1),
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
{
    /* code modified by LLM (iteration 2): [fixed type errors in invariants and added proofs for ensures clauses] */
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 0 <= k < (i as int) && k < l < chords.len() ==> 
                !chord_intersects(&chords[k], &chords[l]),
        decreases n - i,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < j <= n,
                forall|l: int| (i as int) < l < (j as int) ==> !chord_intersects(&chords[i as int], &chords[l]),
            decreases n - j,
        {
            let c1 = &chords[i];
            let c2 = &chords[j];

            let c1_start = if c1[0] < c1[1] { c1[0] } else { c1[1] };
            let c1_end   = if c1[0] > c1[1] { c1[0] } else { c1[1] };
            let c2_start = if c2[0] < c2[1] { c2[0] } else { c2[1] };
            let c2_end   = if c2[0] > c2[1] { c2[0] } else { c2[1] };

            let intersects = (c1_start < c2_start && c2_start < c1_end && c1_end < c2_end) ||
                             (c2_start < c1_start && c1_start < c2_end && c2_end < c1_end);
            
            proof {
                assert(intersects == chord_intersects(c1, c2));
            }

            if intersects {
                assert(chord_intersects(&chords[i as int], &chords[j as int]));
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    assert forall|k: int, l: int| 
        0 <= k < chords.len() && 0 <= l < chords.len() && k != l
        implies !chord_intersects(&chords[k], &chords[l])
    by {
        if l < k {
            lemma_chord_intersects_is_symmetric(&chords[l], &chords[k]);
        }
    };
    
    return false;
}
// </vc-code>

}
fn main() {}