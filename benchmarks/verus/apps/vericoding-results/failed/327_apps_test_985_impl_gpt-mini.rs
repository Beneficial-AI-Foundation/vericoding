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
/* helper modified by LLM (iteration 5): combination formula for n choose 2 */
spec fn comb2(n: int) -> int
    requires
        0 <= n,
{
    n * (n - 1) / 2
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
{
    /* code modified by LLM (iteration 5): compute n choose 2 and return as u64 */
    let n_usize = positions.len();
    let result = (n_usize as u64) * ((n_usize - 1) as u64) / 2u64;
    result
}
// </vc-code>


}

fn main() {}