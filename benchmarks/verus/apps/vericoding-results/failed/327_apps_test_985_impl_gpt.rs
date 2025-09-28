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
/* helper modified by LLM (iteration 5): basic length bounds derived from valid_input */
proof fn lemma_len_bounds(positions: Seq<(int, int)>)
    requires
        valid_input(positions),
    ensures
        1 <= positions.len(),
        positions.len() <= 200000,
{
    assert(positions.len() >= 1);
    assert(positions.len() <= 200000);
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
    /* code modified by LLM (iteration 5): compute n choose 2 directly with arithmetic and proof of safety and correctness */
    let n_usize = positions.len();
    let n: u64 = n_usize as u64;

    proof {
        assert(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int)).len() == positions@.len());
        assert(positions@.len() == positions.len() as int);
        lemma_len_bounds(positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int)));
        assert(1 <= positions.len() as int);
        assert(n as int == positions.len() as int);
        assert(n >= 1);
        assert(n as int <= 200000);
    }

    let nm1: u64 = n - 1;

    proof {
        assert(nm1 as int == n as int - 1);
        assert(0 <= n as int);
        assert(0 <= nm1 as int);
        assert(nm1 as int <= n as int);
        assert(n as int <= 200000);
        assert(nm1 as int <= 200000);
        assert((n as int) * (nm1 as int) <= 200000 * 200000);
        assert(200000 * 200000 <= (18446744073709551615u64 as int));
    }

    let prod: u64 = n * nm1;
    let res: u64 = prod / 2;

    proof {
        let s = positions@.map(|i, p: (i8, i8)| (p.0 as int, p.1 as int));
        reveal(count_attacking_pairs);
        reveal(valid_output);
        assert(s.len() == positions@.len());
        assert(s.len() == positions.len() as int);
        assert(res as int == ((n as int) * (nm1 as int)) / 2);
        assert(res as int == s.len() * (s.len() - 1) / 2);
        assert(valid_input(s));
        assert(0 <= res as int);
        assert(valid_output(s, res as int));
    }

    res
}
// </vc-code>


}

fn main() {}