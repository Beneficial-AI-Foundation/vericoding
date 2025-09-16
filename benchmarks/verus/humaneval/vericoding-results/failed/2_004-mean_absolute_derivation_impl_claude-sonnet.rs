// <vc-preamble>
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

spec fn mean(values: Seq<int>) -> (result:int)
    recommends
        values.len() > 0,
{
    sum(values) / (values.len() as int)
}

spec fn abs(n: int) -> (result:int) {
    if n >= 0 {
        n
    } else {
        -n
    }
}

spec fn spec_mean_absolute_deviation(numbers: Seq<int>) -> (result:int)
    recommends
        numbers.len() > 0,
{
    let avg = mean(numbers);
    sum(numbers.map(|_index, n: int| abs(n - avg))) / (numbers.len() as int)
}

spec fn if_inner_lemma_how_to_add_then_divide(x : int, y : int, d : int) -> (result: bool) {
    if (x % d) + (y % d) >= d {
        &&& (x + y) / d == (x / d) + (y / d) + 1
        &&& (x + y) % d == (x % d) + (y % d) - d
    } else {
        &&& (x + y) / d == (x / d) + (y / d)
        &&& (x + y) % d == (x % d) + (y % d)
    }
}

spec fn expr_inner_divide_i32_by_u32(qr : (i32, u32), x: i32, d: u32) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
spec fn expr_inner_divide_i32_by_usize(qr : (i32, usize), x: i32, d: usize) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// </vc-preamble>

// <vc-helpers>
/* helpers modified by LLM (iteration 5): fixed zip API usage by removing invalid zip method */
proof fn lemma_sum_distributive(s1: Seq<int>, s2: Seq<int>)
    requires
        s1.len() == s2.len(),
    ensures
        s1.len() > 0 ==> sum(s1.add(s2)) == sum(s1) + sum(s2),
{
    if s1.len() == 0 {
        return;
    }
    let combined = s1.add(s2);
    assert(combined.len() == s1.len());
    assert(forall|i: int| 0 <= i < s1.len() ==> combined[i] == s1[i] + s2[i]);
}

proof fn lemma_sum_abs_bounds(numbers: Seq<int>, avg: int)
    requires
        numbers.len() > 0,
    ensures
        sum(numbers.map(|_i, n: int| abs(n - avg))) >= 0,
{
    let abs_seq = numbers.map(|_i, n: int| abs(n - avg));
    assert(forall|i: int| 0 <= i < abs_seq.len() ==> abs_seq[i] >= 0);
}

fn compute_sum(numbers: &[i32]) -> (result: i32)
    requires
        numbers.len() > 0,
    ensures
        result == sum(numbers@.map(|_i, n: i32| n as int)),
{
    let mut total = 0i32;
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            total == sum(numbers@.take(i as int).map(|_idx, n: i32| n as int)),
    {
        total = total + numbers[i];
        i = i + 1;
    }
    total
}

fn compute_abs_sum(numbers: &[i32], avg: i32) -> (result: u32)
    requires
        numbers.len() > 0,
    ensures
        result == sum(numbers@.map(|_i, n: i32| abs(n as int - avg as int))) as u32,
{
    let mut total = 0u32;
    let mut i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            total == sum(numbers@.take(i as int).map(|_idx, n: i32| abs(n as int - avg as int))) as u32,
    {
        let diff = if numbers[i] >= avg { numbers[i] - avg } else { avg - numbers[i] };
        total = total + diff as u32;
        i = i + 1;
    }
    total
}
// </vc-helpers>

// <vc-spec>
fn mean_absolute_deviation(numbers: &[i32]) -> (result: u32)

    requires
        numbers.len() > 0,

    ensures
        result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed implementation without verification bypasses */
    let total = compute_sum(numbers);
    let avg = total / numbers.len() as i32;
    let abs_sum = compute_abs_sum(numbers, avg);
    let result = abs_sum / numbers.len() as u32;
    result
}
// </vc-code>

}
fn main() {}