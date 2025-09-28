// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(positions: Seq<(int, int)>) -> bool {
    positions.len() >= 1 && positions.len() <= 200000 &&
    (forall|i: int| 0 <= i < positions.len() ==> 
        1 <= #[trigger] positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall|i: int, j: int| 0 <= i < j < positions.len() ==> 
        #[trigger] positions[i] != #[trigger] positions[j])
}

spec fn count_attacking_pairs(positions: Seq<(int, int)>) -> int
    recommends valid_input(positions)
{
    /* Count pairs (i,j) where i < j and bishops at positions[i] and positions[j] attack each other */
    positions.len() * (positions.len() - 1) / 2 /* placeholder - actual implementation would count diagonal pairs */
}

spec fn valid_output(positions: Seq<(int, int)>, result: int) -> bool
    recommends valid_input(positions)
{
    result == count_attacking_pairs(positions) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed set comprehension syntax by using curly braces */
spec fn is_on_diagonal(p1: (int, int), p2: (int, int)) -> bool {
    (p1.0 - p2.0).abs() == (p1.1 - p2.1).abs()
}

/* helper modified by LLM (iteration 5): fixed set comprehension syntax by using curly braces */
spec fn count_diagonal_pairs(positions: Seq<(int, int)>) -> int
    recommends valid_input(positions)
{
    let n = positions.len();
    if n <= 1 {
        0
    } else {
        { (i, j) | 0 <= i < j < n && is_on_diagonal(positions[i], positions[j]) }.len()
    }
}
// </vc-helpers>

// <vc-spec>
fn solve_bishops(positions: Vec<(i8, i8)>) -> (result: u64)
    requires
        valid_input(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int))),
    ensures
        valid_output(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int)), result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed set comprehension syntax by using curly braces */
{
    let n = positions.len();
    if n <= 1 {
        0
    } else {
        let mut count = 0;
        let mut i = 0;
        while i < n
            invariant 0 <= i <= n,
            invariant count == { (a, b) | 
                0 <= a < b < n && a < i && 
                is_on_diagonal(
                    (positions@[a].0 as int, positions@[a].1 as int),
                    (positions@[b].0 as int, positions@[b].1 as int)
                )
            }.len(),
            decreases n - i
        {
            let mut j = i + 1;
            while j < n
                invariant i + 1 <= j <= n,
                invariant count == { (a, b) | 
                    0 <= a < b < n && a < i && 
                    is_on_diagonal(
                        (positions@[a].0 as int, positions@[a].1 as int),
                        (positions@[b].0 as int, positions@[b].1 as int)
                    )
                }.len() + { k | 
                    i+1 <= k < j && 
                    is_on_diagonal(
                        (positions@[i].0 as int, positions@[i].1 as int),
                        (positions@[k].0 as int, positions@[k].1 as int)
                    )
                }.len(),
                decreases n - j
            {
                let p1 = (positions@[i].0 as int, positions@[i].1 as int);
                let p2 = (positions@[j].0 as int, positions@[j].1 as int);
                if is_on_diagonal(p1, p2) {
                    count = count + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        count as u64
    }
}
// </vc-code>


}

fn main() {}