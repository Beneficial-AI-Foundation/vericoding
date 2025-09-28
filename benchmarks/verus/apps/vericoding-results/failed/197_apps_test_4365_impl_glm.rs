// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k: int) -> bool {
    2 <= k <= 100
}

spec fn count_odd_numbers(k: int) -> int
    recommends k >= 1
{
    (k + 1) / 2
}

spec fn count_even_numbers(k: int) -> int
    recommends k >= 1
{
    k / 2
}

spec fn expected_result(k: int) -> int
    recommends valid_input(k)
{
    count_odd_numbers(k) * count_even_numbers(k)
}

spec fn correct_result(k: int, result: int) -> bool
    recommends valid_input(k)
{
    result == expected_result(k)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed compilation by using i8 arithmetic */
fn count_odd_exec(k: i8) -> i8 {
    (k + 1) / 2
}

/* helper modified by LLM (iteration 2): fixed compilation by using i8 arithmetic */
fn count_even_exec(k: i8) -> i8 {
    k / 2
}
// </vc-helpers>

// <vc-spec>
fn count_even_odd_pairs(k: i8) -> (result: i8)
    requires
        valid_input(k as int),
    ensures
        correct_result(k as int, result as int),
        result >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation by removing int usage */
    let odd_count = count_odd_exec(k);
    let even_count = count_even_exec(k);
    (odd_count as i16 * even_count as i16) as i8
}
// </vc-code>


}

fn main() {}