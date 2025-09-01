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
}

proof fn lemma_abs_is_nonnegative(n: int)
    ensures
        abs(n) >= 0,
{
    if n >= 0 {
        assert(abs(n) == n);
    } else {
        assert(abs(n) == -n);
    }
}

proof fn lemma_abs_triangle_inequality(x: int, y: int)
    ensures
        abs(x + y) <= abs(x) + abs(y),
{
    if x >= 0 {
        if y >= 0 {
            assert(abs(x + y) == x + y);
            assert(abs(x) + abs(y) == x + y);
        } else {
            if x + y >= 0 {
                assert(abs(x + y) == x + y);
                assert(abs(x) + abs(y) == x - y);
                assert(x + y <= x - y);
            } else {
                assert(abs(x + y) == -(x + y));
                assert(abs(x) + abs(y) == x - y);
                assert(-(x + y) <= x - y);
            }
        }
    } else {
        if y >= 0 {
            if x + y >= 0 {
                assert(abs(x + y) == x + y);
                assert(abs(x) + abs(y) == -x + y);
                assert(x + y <= -x + y);
            } else {
                assert(abs(x + y) == -(x + y));
                assert(abs(x) + abs(y) == -x + y);
                assert(-(x + y) <= -x + y);
            }
        } else {
            assert(abs(x + y) == -(x + y));
            assert(abs(x) + abs(y) == -x - y);
        }
    }
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
    let mut count = 0;
    let mut sum_abs_dev = 0;
    let mut sum_nums = 0;
    
    // First pass: calculate sum
    for i in 0..n
        invariant
            0 <= i <= n,
            sum_nums == sum(numbers@.subrange(0, i as int).map(|_index, n: i32| n as int)),
    {
        sum_nums += numbers[i] as int;
    }
    
    assert(sum_nums == sum(numbers@.map(|_index, n: i32| n as int)));
    
    let avg = sum_nums / (n as int);
    
    // Second pass: calculate sum of absolute deviations
    for i in 0..n
        invariant
            0 <= i <= n,
            sum_abs_dev == sum(numbers@.subrange(0, i as int).map(|_index, n: i32| abs(n as int - avg))),
    {
        let dev = numbers[i] as int - avg;
        let abs_dev = if dev >= 0 { dev } else { -dev };
        sum_abs_dev += abs_dev;
    }
    
    assert(sum_abs_dev == sum(numbers@.map(|_index, n: i32| abs(n as int - avg))));
    
    let result = sum_abs_dev / (n as int);
    
    lemma_mean_absolute_deviation_properties(numbers@.map(|_index, n: i32| n as int));
    assert(result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)));
    
    result as u32
}
// </vc-code>

fn main() {}
}