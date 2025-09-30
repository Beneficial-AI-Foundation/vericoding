// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int, b: int, c: int, d: int) -> bool {
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

spec fn min(x: int, y: int) -> int {
    if x < y { x } else { y }
}

spec fn max(x: int, y: int) -> int {
    if x > y { x } else { y }
}

spec fn interval_overlap_length(a: int, b: int, c: int, d: int) -> int {
    if min(b, d) - max(a, c) > 0 { min(b, d) - max(a, c) } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove overlap computation matches spec */
fn overlap_computation_refines(a: int, b: int, c: int, d: int, m1: int, M1: int, overlap: int, res: int)
    requires
        valid_input(a, b, c, d),
        m1 == if b < d { b } else { d },
        M1 == if a > c { a } else { c },
        overlap == m1 - M1,
        res == if overlap > 0 { overlap } else { 0 },
    ensures
        res == interval_overlap_length(a, b, c, d),
{
    proof {
        assert(min(b, d) == if b < d { b } else { d });
        assert(max(a, c) == if a > c { a } else { c });
        assert(min(b, d) - max(a, c) == m1 - M1);
        if min(b, d) - max(a, c) > 0 {
            assert(interval_overlap_length(a, b, c, d) == min(b, d) - max(a, c));
            assert(res == min(b, d) - max(a, c));
        } else {
            assert(interval_overlap_length(a, b, c, d) == 0);
            assert(res == 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8, b: i8, c: i8, d: i8) -> (result: i8)
    requires
        valid_input(a as int, b as int, c as int, d as int),
    ensures
        result >= 0,
        result as int == interval_overlap_length(a as int, b as int, c as int, d as int),
        result <= 100,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): compute overlap using i8 runtime values and prove spec equivalence inline without calling helper */
    let m1_i8: i8 = if b < d { b } else { d };
    let M1_i8: i8 = if a > c { a } else { c };
    let overlap_i8: i8 = m1_i8 - M1_i8;
    let res_i8: i8 = if overlap_i8 > 0 { overlap_i8 } else { 0 };
    proof {
        let ai: int = a as int;
        let bi: int = b as int;
        let ci: int = c as int;
        let di: int = d as int;
        let m1: int = if bi < di { bi } else { di };
        let M1: int = if ai > ci { ai } else { ci };
        let overlap: int = m1 - M1;
        let res_i: int = if overlap > 0 { overlap } else { 0 };
        assert(m1 == m1_i8 as int);
        assert(M1 == M1_i8 as int);
        assert(overlap == overlap_i8 as int);
        if overlap > 0 {
            assert(res_i == overlap);
            assert(res_i8 as int == overlap);
        } else {
            assert(res_i == 0);
            assert(res_i8 == 0);
        }
        assert(res_i == res_i8 as int);
    }
    res_i8
}
// </vc-code>


}

fn main() {}