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
spec fn attacking(pos1: (int, int), pos2: (int, int)) -> bool {
    (pos1.0 + pos1.1 == pos2.0 + pos2.1) ||
    (pos1.0 - pos1.1 == pos2.0 - pos2.1)
}

/* helper modified by LLM (iteration 5): fixed typo in spec function for checking if two bishop positions attack each other using int types */

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
{
/* code modified by LLM (iteration 5): fixed variable names, typos, and added proper invariants and ensures conditions */
    fn attacking_local(p1: (i8, i8), p2: (i8, i8)) -> bool {
        (p1.0 as int + p1.1 as int == p2.0 as int + p2.1 as int) ||
        (p1.0 as int - p1.1 as int == p2.0 as int - p2.1 as int)
    }
    let mut result = 0u64;
    let mut i = 0usize;
    while i < positions.len()
        invariant
            i <= positions.len(),
            0 <= i,
            result as int >= 0,
        decreases positions.len() - i
    {
        let mut j = 0usize;
        while j < i
            invariant
                j <= i,
                0 <= j,
                0 < i <= positions.len(),
                result as int >= 0,
            decreases i - j
        {
            if attacking_local(positions@[j], positions@[i as usize]) {
                result += 1u64;
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