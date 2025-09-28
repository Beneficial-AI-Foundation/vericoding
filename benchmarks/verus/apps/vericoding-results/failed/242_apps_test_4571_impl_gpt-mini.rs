// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    1 <= n <= 100 && 1 <= m <= n && m <= 5
}

spec fn power(base: int, exp: int) -> int
    decreases exp when exp >= 0
{
    if exp <= 0 { 1 } else { base * power(base, exp - 1) }
}

spec fn expected_time(n: int, m: int) -> int {
    (1900 * m + 100 * (n - m)) * power(2, m)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define coins helper as spec fn */
spec fn coins(n: int, m: int) -> int {
    1900 * m + 100 * (n - m)
}

/* helper modified by LLM (iteration 5): lemma unfolding expected_time into coins * power */
fn expected_time_unfold(n: int, m: int)
    requires
        valid_input(n, m),
    ensures
        expected_time(n, m) == coins(n, m) * power(2, m),
{
    proof {
        assert(expected_time(n, m) == (1900 * m + 100 * (n - m)) * power(2, m));
        assert(coins(n, m) == 1900 * m + 100 * (n - m));
        assert(expected_time(n, m) == coins(n, m) * power(2, m));
    }
}

/* helper modified by LLM (iteration 5): lemma relating power(2,m) to concrete values for 1..5 */
fn power_two(m: int)
    requires
        1 <= m <= 5,
    ensures
        power(2, m) == if m == 1 { 2 } else if m == 2 { 4 } else if m == 3 { 8 } else if m == 4 { 16 } else { 32 },
{
    proof {
        if m == 1 {
            assert(power(2, m) == 2);
        } else if m == 2 {
            assert(power(2, m) == 4);
        } else if m == 3 {
            assert(power(2, m) == 8);
        } else if m == 4 {
            assert(power(2, m) == 16);
        } else {
            assert(power(2, m) == 32);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires valid_input(n as int, m as int)
    ensures result as int == expected_time(n as int, m as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute answer using integer arithmetic and prove spec equality */
{
    let n_i64: i64 = n as i64;
    let m_i64: i64 = m as i64;

    let coins_i64: i64 = 1900 * m_i64 + 100 * (n_i64 - m_i64);
    let p_i64: i64 = if m == 1 { 2 } else if m == 2 { 4 } else if m == 3 { 8 } else if m == 4 { 16 } else { 32 };
    let total_i64: i64 = coins_i64 * p_i64;
    let result_i8: i8 = total_i64 as i8;

    proof {
        let n_i: int = n as int;
        let m_i: int = m as int;

        expected_time_unfold(n_i, m_i);
        power_two(m_i);

        assert((coins_i64 as int) == coins(n_i, m_i));
        assert((p_i64 as int) == power(2, m_i));
        assert((total_i64 as int) == coins(n_i, m_i) * power(2, m_i));
    }

    result_i8
}

// </vc-code>


}

fn main() {}