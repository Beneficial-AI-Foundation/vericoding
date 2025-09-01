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
proof fn lemma_mean_absolute_deviation_properties(numbers: Seq<int>)
    requires
        numbers.len() > 0,
{
    let avg = mean(numbers);
    let abs_deviations = numbers.map(|_index, n: int| abs(n - avg));
    
    assert(sum(abs_deviations) >= 0);
    assert(spec_mean_absolute_deviation(numbers) == sum(abs_deviations) / (numbers.len() as int));
    
    proof {
        lemma_div_is_ordered(sum(abs_deviations), numbers.len() as int, 0);
    }
}

proof fn lemma_sum_abs_dev_nonnegative(numbers: Seq<int>, avg: int)
    ensures
        sum(numbers.map(|_index, n: int| abs(n - avg))) >= 0,
{
    assert(forall|i: int| 0 <= i < numbers.len() ==> #[trigger] abs(numbers[i] - avg) >= 0);
}
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
    let n = numbers.len();
    let mut sum_nums = 0;
    let mut sum_abs_dev = 0;
    
    // First pass: calculate sum
    for i in 0..n
        invariant
            0 <= i <= n,
            sum_nums == sum(numbers@.take(i as nat).map(|n| n as int)),
    {
        sum_nums += numbers[i] as int;
    }
    
    assert(sum_nums == sum(numbers@.take(n as nat).map(|n| n as int)));
    
    let avg = sum_nums / (n as int);
    
    // Second pass: calculate sum of absolute deviations
    for i in 0..n
        invariant
            0 <= i <= n,
            sum_abs_dev == sum(numbers@.take(i as nat).map(|n| abs(n as int - avg))),
    {
        let dev = numbers[i] as int - avg;
        let abs_dev = if dev >= 0 { dev } else { -dev };
        sum_abs_dev += abs_dev;
    }
    
    assert(sum_abs_dev == sum(numbers@.take(n as nat).map(|n| abs(n as int - avg))));
    
    lemma_sum_abs_dev_nonnegative(numbers@.map(|n| n as int), avg);
    let result = sum_abs_dev / (n as int);
    assert(result >= 0); // because sum_abs_dev >=0 and n>0
    
    lemma_mean_absolute_deviation_properties(numbers@.map(|n| n as int));
    assert(result == spec_mean_absolute_deviation(numbers@.map(|n| n as int)));
    
    result as u32
}
// </vc-code>

fn main() {}
}