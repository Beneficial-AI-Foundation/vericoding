// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n >= 1 && m >= 1
}

spec fn count_face_down_cards(n: int, m: int) -> int
    recommends valid_input(n, m)
{
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        m - 2
    } else if m == 1 {
        n - 2
    } else {
        (n - 2) * (m - 2)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow check helpers for safe arithmetic operations */
fn safe_sub_i8(a: i8, b: i8) -> (result: i8)
    requires a >= b
    ensures result == a - b
{
    a - b
}

fn safe_mul_i8(a: i8, b: i8) -> (result: i8)
    requires a >= 0 && b >= 0 && a as int * b as int <= 127
    ensures result as int == a as int * b as int
{
    a * b
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int),
    ensures 
        result as int == count_face_down_cards(n as int, m as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added explicit overflow checks and used safe arithmetic functions */
    if n == 1 && m == 1 {
        1
    } else if n == 1 {
        assert(m >= 1);
        assert(m >= 2);
        safe_sub_i8(m, 2)
    } else if m == 1 {
        assert(n >= 1);
        assert(n >= 2);
        safe_sub_i8(n, 2)
    } else {
        assert(n >= 2 && m >= 2);
        let n_minus_2 = safe_sub_i8(n, 2);
        let m_minus_2 = safe_sub_i8(m, 2);
        assert(n_minus_2 >= 0 && m_minus_2 >= 0);
        assert(n_minus_2 as int * m_minus_2 as int <= 127);
        safe_mul_i8(n_minus_2, m_minus_2)
    }
}
// </vc-code>


}

fn main() {}