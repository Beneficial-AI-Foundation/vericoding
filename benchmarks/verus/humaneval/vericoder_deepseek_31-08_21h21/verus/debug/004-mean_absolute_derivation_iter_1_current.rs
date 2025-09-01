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
proof fn lemma_div_mod_relation(x: int, d: int)
    requires
        d > 0,
    ensures
        x == d * (x / d) + (x % d),
        x % d >= 0,
        x % d < d,
{
    lemma_fundamental_div_mod(x, d);
}

proof fn lemma_div_mod_relation_converse(x: int, d: int)
    requires
        d > 0,
    ensures
        x / d == (x - (x % d)) / d,
{
    lemma_fundamental_div_mod_converse(x, d);
}

proof fn lemma_abs_properties(n: int)
    ensures
        abs(n) >= 0,
        abs(n) == if n >= 0 { n } else { -n },
{
}

proof fn lemma_sum_map_abs_deviation(numbers: Seq<int>, avg: int)
    ensures
        sum(numbers.map(|_index, n: int| abs(n - avg))) >= 0,
{
    if numbers.len() > 0 {
        lemma_abs_properties(numbers[0] - avg);
    }
}

proof fn lemma_div_nonnegative(numerator: int, denominator: int)
    requires
        denominator > 0,
        numerator >= 0,
    ensures
        numerator / denominator >= 0,
{
    lemma_div_is_ordered(numerator, denominator);
}

proof fn lemma_div_lt_denominator(numerator: int, denominator: int)
    requires
        denominator > 0,
        numerator >= 0,
        numerator < denominator,
    ensures
        numerator / denominator == 0,
{
    lemma_div_is_ordered_by_denominator(numerator, denominator);
}

proof fn lemma_div_multiples_vanish_specific(x: int, d: int)
    requires
        d > 0,
    ensures
        (d * (x / d)) / d == x / d,
{
    lemma_div_multiples_vanish(x, d);
}

proof fn lemma_mod_add_property(x: int, y: int, d: int)
    requires
        d > 0,
    ensures
        (x + y) % d == (x % d + y % d) % d,
{
    lemma_fundamental_div_mod(x + y, d);
    lemma_fundamental_div_mod(x, d);
    lemma_fundamental_div_mod(y, d);
}

proof fn lemma_div_add_property(x: int, y: int, d: int)
    requires
        d > 0,
    ensures
        (x + y) / d == x / d + y / d + ((x % d + y % d) / d),
{
    lemma_fundamental_div_mod(x + y, d);
    lemma_fundamental_div_mod(x, d);
    lemma_fundamental_div_mod(y, d);
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
    let len = numbers.len();
    let mut total_sum: i64 = 0;
    let mut i: usize = 0;
    
    while i < len
        invariant
            i <= len,
            total_sum == sum(numbers@.subrange(0, i).map(|_index, n: i32| n as int)),
    {
        total_sum = total_sum + numbers[i] as i64;
        i = i + 1;
    }
    
    let avg_int = total_sum / (len as i64);
    let avg_i32 = avg_int as i32;
    
    let mut total_abs_dev: u64 = 0;
    let mut j: usize = 0;
    
    while j < len
        invariant
            j <= len,
            total_abs_dev as int == sum(numbers@.subrange(0, j).map(|_index, n: int| abs(n - avg_int))),
    {
        let diff = (numbers[j] as i64 - avg_int).abs() as u64;
        total_abs_dev = total_abs_dev + diff;
        j = j + 1;
    }
    
    let result = (total_abs_dev / (len as u64)) as u32;
    
    proof {
        lemma_div_nonnegative(total_abs_dev as int, len as int);
        lemma_div_lt_denominator(total_abs_dev as int, len as int);
        lemma_div_multiples_vanish_specific(total_abs_dev as int, len as int);
        lemma_mod_add_property(total_abs_dev as int, 0, len as int);
        lemma_div_add_property(total_abs_dev as int, 0, len as int);
        lemma_sum_map_abs_deviation(numbers@.map(|_index, n: i32| n as int), avg_int);
    }
    
    result
}
// </vc-code>

fn main() {}
}