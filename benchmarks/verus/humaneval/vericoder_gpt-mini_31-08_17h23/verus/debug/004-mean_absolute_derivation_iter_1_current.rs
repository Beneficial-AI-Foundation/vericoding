use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_div_is_ordered_by_denominator, lemma_div_multiples_vanish,
    lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse,
};
use vstd::arithmetic::mul::{
    lemma_mul_inequality, lemma_mul_is_distributive_add, lemma_mul_is_distributive_add_other_way,
    lemma_mul_unary_negation,
};
use vstd::prelude::*;

verus! {

spec fn sum(numbers: Seq<int>) -> (result:int) {
    numbers.fold_left(0, |acc: int, x| acc + x)
}
// pure-end
// pure-end

spec fn mean(values: Seq<int>) -> (result:int)
    recommends
        values.len() > 0,
{
    sum(values) / (values.len() as int)
}
// pure-end
// pure-end

spec fn abs(n: int) -> (result:int) {
    if n >= 0 {
        n
    } else {
        -n
    }
}
// pure-end
// pure-end

spec fn spec_mean_absolute_deviation(numbers: Seq<int>) -> (result:int)
    recommends
        numbers.len() > 0,
{
    let avg = mean(numbers);
    sum(numbers.map(|_index, n: int| abs(n - avg))) / (numbers.len() as int)
}
// pure-end
// pure-end

spec fn if_inner_lemma_how_to_add_then_divide(x : int, y : int, d : int) -> (result: bool) {
    if (x % d) + (y % d) >= d {
        &&& (x + y) / d == (x / d) + (y / d) + 1
        &&& (x + y) % d == (x % d) + (y % d) - d
    } else {
        &&& (x + y) / d == (x / d) + (y / d)
        &&& (x + y) % d == (x % d) + (y % d)
    }
}
// pure-end
// pure-end


spec fn expr_inner_divide_i32_by_u32(qr : (i32, u32), x: i32, d: u32) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end
spec fn expr_inner_divide_i32_by_usize(qr : (i32, usize), x: i32, d: usize) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end

// <vc-helpers>
// No additional helper lemmas needed for this proof; kept intentionally empty.
// </vc-helpers>

// <vc-spec>
fn mean_absolute_deviation(numbers: &[i32]) -> (result: u32)
    // pre-conditions-start
    requires
        numbers.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let len_usize: usize = numbers.len();
    let len_int: int = len_usize as int;

    // First, compute the sum as a mathematical int
    let mut i: usize = 0;
    let mut s: int = 0;
    while i < len_usize
        invariant i <= len_usize
        invariant s == sum(numbers@.slice(0, i).map(|_j, x: i32| x as int))
    {
        let xi: i32 = numbers[i];
        s = s + (xi as int);
        i = i + 1;
    }

    // Compute the average as spec does (integer division)
    let avg: int = s / len_int;

    // Now compute the sum of absolute deviations as a mathematical int
    let mut j: usize = 0;
    let mut sum_abs: int = 0;
    while j < len_usize
        invariant j <= len_usize
        invariant sum_abs
            == sum(
                numbers@.slice(0, j).map(|_k, x: i32| {
                    let diff: int = (x as int) - avg;
                    if diff >= 0 { diff } else { -diff }
                })
            )
    {
        let xj: i32 = numbers[j];
        let diff: int = (xj as int) - avg;
        let ad: int = if diff >= 0 { diff } else { -diff };
        sum_abs = sum_abs + ad;
        j = j + 1;
    }

    // Final result: integer division of sum_abs by len_int, then return as u32
    let res_int: int = sum_abs / len_int;
    // res_int is >= 0 because it's a sum of absolute values divided by positive len_int
    proof {
        // sum of absolute values is non-negative
        assert(sum_abs >= 0);
        assert(len_int > 0);
        assert(res_int >= 0);
    }
    let result_u32: u32 = res_int as u32;
    result_u32
    // impl-end
}
// </vc-code>

fn main() {}
}