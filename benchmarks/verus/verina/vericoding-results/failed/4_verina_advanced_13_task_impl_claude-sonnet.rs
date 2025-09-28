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
/* helper modified by LLM (iteration 5): fixed type mismatches for int vs usize */
proof fn lemma_chord_intersects_equiv(chord1: &Vec<usize>, chord2: &Vec<usize>, a1: usize, b1: usize, a2: usize, b2: usize)
    requires
        chord1.len() == 2,
        chord2.len() == 2,
        a1 == if chord1[0] < chord1[1] { chord1[0] } else { chord1[1] },
        b1 == if chord1[0] > chord1[1] { chord1[0] } else { chord1[1] },
        a2 == if chord2[0] < chord2[1] { chord2[0] } else { chord2[1] },
        b2 == if chord2[0] > chord2[1] { chord2[0] } else { chord2[1] },
    ensures
        chord_intersects(chord1, chord2) == ((a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1))
{
}

fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
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
    /* code modified by LLM (iteration 5): fixed type mismatches by casting indices */
    let mut i = 0;
    while i < chords.len()
        invariant
            0 <= i <= chords.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < chords.len() && x != y ==> !chord_intersects(&chords[x], &chords[y]),
        decreases chords.len() - i
    {
        let mut j = 0;
        while j < chords.len()
            invariant
                0 <= j <= chords.len(),
                0 <= i < chords.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < chords.len() && x != y ==> !chord_intersects(&chords[x], &chords[y]),
                forall|y: int| 0 <= y < j && i != y ==> !chord_intersects(&chords[i as int], &chords[y]),
            decreases chords.len() - j
        {
            if i != j {
                assert(chords[i as int].len() == 2) by {
                    assert(0 <= i < chords.len());
                }
                assert(chords[j as int].len() == 2) by {
                    assert(0 <= j < chords.len());
                }
                
                let a1 = min(chords[i][0], chords[i][1]);
                let b1 = max(chords[i][0], chords[i][1]);
                let a2 = min(chords[j][0], chords[j][1]);
                let b2 = max(chords[j][0], chords[j][1]);
                
                proof {
                    lemma_chord_intersects_equiv(&chords[i as int], &chords[j as int], a1, b1, a2, b2);
                }
                
                if (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1) {
                    return true;
                }
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