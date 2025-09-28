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
/* helper modified by LLM (iteration 5): executable and proof helpers for intersection */
fn intersects_exec(c1: &Vec<usize>, c2: &Vec<usize>) -> bool {
    let a1 = if c1[0] < c1[1] { c1[0] } else { c1[1] };
    let b1 = if c1[0] > c1[1] { c1[0] } else { c1[1] };
    let a2 = if c2[0] < c2[1] { c2[0] } else { c2[1] };
    let b2 = if c2[0] > c2[1] { c2[0] } else { c2[1] };
    (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)
}

/* helper modified by LLM (iteration 5): proof connecting spec-level chord_intersects to executable intersects_exec */
proof fn lemma_intersection_equiv(chords: &Vec<Vec<usize>>, i: int, j: int)
    ensures chord_intersects(&chords[i as usize], &chords[j as usize]) == intersects_exec(&chords[i as usize], &chords[j as usize])
{
    proof {
        let c1 = &chords[i as usize];
        let c2 = &chords[j as usize];
        let a1 = if c1[0] < c1[1] { c1[0] } else { c1[1] };
        let b1 = if c1[0] > c1[1] { c1[0] } else { c1[1] };
        let a2 = if c2[0] < c2[1] { c2[0] } else { c2[1] };
        let b2 = if c2[0] > c2[1] { c2[0] } else { c2[1] };
        assert(chord_intersects(c1, c2) == ((a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)));
        assert(intersects_exec(c1, c2) == ((a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)));
        assert(chord_intersects(c1, c2) == intersects_exec(c1, c2));
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
    /* code modified by LLM (iteration 5): iterate pairs and detect any intersecting chord */
    let mut result: bool = false;
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result == exists|a: int, b: int|
                0 <= a && a < b && b < n as int &&
                (a < i as int) &&
                #[trigger] chord_intersects(&chords[a as usize], &chords[b as usize]),
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < n,
                j <= n,
                result == exists|a: int, b: int|
                    0 <= a && a < b && b < n as int &&
                    ((a < i as int) || (a == i as int && b <= j as int)) &&
                    #[trigger] chord_intersects(&chords[a as usize], &chords[b as usize]),
            decreases n - j
        {
            if !result {
                if intersects_exec(&chords[i], &chords[j]) {
                    result = true;
                    proof {
                        lemma_intersection_equiv(chords, i as int, j as int);
                        assert(chord_intersects(&chords[i as usize], &chords[j as usize]));
                        assert(exists|a: int, b: int| a == i as int && b == j as int && 0 <= a && a < b && b < n as int && chord_intersects(&chords[a as usize], &chords[b as usize]));
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}