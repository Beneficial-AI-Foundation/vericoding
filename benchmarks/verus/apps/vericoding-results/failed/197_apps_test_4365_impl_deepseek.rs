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
proof fn lemma_arithmetic_safe_conversion(k: int)
    requires
        2 <= k <= 100,
    ensures
        (k + 1) as i8 >= 0,
        k as i8 >= 0,
{
}

proof fn lemma_count_conversions(k: int)
    requires
        2 <= k <= 100,
    ensures
        ((k + 1) / 2) as i8 == count_odd_numbers(k) as i8,
        (k / 2) as i8 == count_even_numbers(k) as i8,
{
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
    /* code modified by LLM (iteration 5): Fixed type conversion issues in executable code */
    assert(2 <= k as int && k as int <= 100);
    
    proof {
        lemma_arithmetic_safe_conversion(k as int);
        lemma_even_odd_bounds(k as int);
        lemma_expected_result_bounds(k as int);
        lemma_count_conversions(k as int);
    }
    
    let k_native: i8 = k;
    let odd_count: i8 = ((k_native + 1) / 2);
    let even_count: i8 = (k_native / 2);
    let total_pairs: i8 = odd_count * even_count;
    
    total_pairs
}
// </vc-code>


}

fn main() {}