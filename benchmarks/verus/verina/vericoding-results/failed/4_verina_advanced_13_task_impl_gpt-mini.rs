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
/* helper modified by LLM (iteration 5): prove runtime computation implies spec predicate */
proof fn chord_intersects_from_vals(ch1: &Vec<usize>, ch2: &Vec<usize>, a1: usize, b1: usize, a2: usize, b2: usize, inter: bool)
    requires
        ch1.len() == 2,
        ch2.len() == 2,
        a1 == if ch1[0] < ch1[1] { ch1[0] } else { ch1[1] },
        b1 == if ch1[0] > ch1[1] { ch1[0] } else { ch1[1] },
        a2 == if ch2[0] < ch2[1] { ch2[0] } else { ch2[1] },
        b2 == if ch2[0] > ch2[1] { ch2[0] } else { ch2[1] },
        inter == ((a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)),
    ensures
        chord_intersects(ch1, ch2) == inter,
{
    proof {
        assert(chord_intersects(ch1, ch2) == ((a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1)));
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
    /* code modified by LLM (iteration 5): replaced int counters with usize and added proof linking runtime inter to spec */
    let mut i: usize = 0;
    let mut res: bool = false;
    while i < chords.len()
        invariant
            0 <= (i as int),
            (i as int) <= (chords.len() as int),
            res == exists|p: int, q: int|
                0 <= p < (i as int) && 0 <= q < (chords.len() as int) && p != q &&
                #[trigger] chord_intersects(&chords[p as usize], &chords[q as usize]),
        decreases chords.len() - i
    {
        let mut j: usize = 0;
        while j < chords.len()
            invariant
                0 <= (j as int),
                (j as int) <= (chords.len() as int),
                res == (exists|p: int, q: int|
                            0 <= p < (i as int) && 0 <= q < (chords.len() as int) && p != q &&
                            #[trigger] chord_intersects(&chords[p as usize], &chords[q as usize])
                        ) || (exists|q2: int|
                            0 <= q2 < (j as int) && q2 != (i as int) &&
                            #[trigger] chord_intersects(&chords[i], &chords[q2])
                        ),
            decreases chords.len() - j
        {
            if i != j {
                let a1 = if chords[i][0] < chords[i][1] { chords[i][0] } else { chords[i][1] };
                let b1 = if chords[i][0] > chords[i][1] { chords[i][0] } else { chords[i][1] };
                let a2 = if chords[j][0] < chords[j][1] { chords[j][0] } else { chords[j][1] };
                let b2 = if chords[j][0] > chords[j][1] { chords[j][0] } else { chords[j][1] };
                let inter = (a1 < a2 && a2 < b1 && b1 < b2) || (a2 < a1 && a1 < b2 && b2 < b1);
                if inter {
                    proof {
                        chord_intersects_from_vals(&chords[i], &chords[j], a1, b1, a2, b2, inter);
                        assert(chord_intersects(&chords[i], &chords[j]));
                        assert(exists|q2: int| 0 <= q2 < ((j as int) + 1) && q2 != (i as int) && chord_intersects(&chords[i], &chords[q2]));
                    }
                    res = true;
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}