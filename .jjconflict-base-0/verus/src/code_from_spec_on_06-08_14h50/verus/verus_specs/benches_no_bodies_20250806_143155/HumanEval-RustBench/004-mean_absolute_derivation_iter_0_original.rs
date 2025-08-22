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

spec fn mean(values: Seq<int>) -> (result:int)
    recommends
        values.len() > 0,
{
    sum(values) / (values.len() as int)
}
// pure-end

spec fn abs(n: int) -> (result:int) {
    if n >= 0 {
        n
    } else {
        -n
    }
}
// pure-end

spec fn spec_mean_absolute_deviation(numbers: Seq<int>) -> (result:int)
    recommends
        numbers.len() > 0,
{
    let avg = mean(numbers);
    sum(numbers.map(|_index, n: int| abs(n - avg))) / (numbers.len() as int)
}
// pure-end

proof fn lemma_sum_bound(numbers: Seq<int>, min: int, max: int)
    // pre-conditions-start
    requires
        forall|i| 0 <= i < numbers.len() ==> min <= #[trigger] numbers[i] <= max,
    // pre-conditions-end
    // post-conditions-start
    ensures
        numbers.len() * min <= sum(numbers) <= numbers.len() * max,
    decreases numbers.len(),
    // post-conditions-end
{
    // impl-start
    if numbers.len() != 0 {
        lemma_sum_bound(numbers.drop_last(), min, max);
        lemma_mul_is_distributive_add_other_way(min, numbers.len() - 1, 1);
        lemma_mul_is_distributive_add_other_way(max, numbers.len() - 1, 1);
    }
    // impl-end
}
// pure-end

proof fn lemma_sum_ratio_bound(numbers: Seq<int>, denominator: int, min: int, max: int)
    // pre-conditions-start
    requires
        forall|i| 0 <= i < numbers.len() ==> min <= #[trigger] numbers[i] <= max,
        denominator >= numbers.len(),
        denominator > 0,
        min <= 0,
        max >= 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        min <= sum(numbers) / denominator <= max,
    // post-conditions-end
{
    // impl-start
    lemma_sum_bound(numbers, min, max);
    assert(denominator * min <= numbers.len() * min) by {
        lemma_mul_unary_negation(denominator, -min);
        lemma_mul_unary_negation(numbers.len() as int, -min);
        lemma_mul_inequality(numbers.len() as int, denominator, -min);
    }
    assert(numbers.len() * max <= denominator * max) by {
        lemma_mul_inequality(numbers.len() as int, denominator, max);
    }
    lemma_div_multiples_vanish(min, denominator);
    lemma_div_multiples_vanish(max, denominator);
    lemma_div_is_ordered(denominator * min, sum(numbers), denominator);
    lemma_div_is_ordered(sum(numbers), denominator * max, denominator);
    // impl-end
}
// pure-end

proof fn lemma_how_to_update_running_sum(s: Seq<int>, i: int)
    // pre-conditions-start
    requires
        0 <= i < s.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        sum(s.take(i + 1)) == sum(s.take(i)) + s[i],
    // post-conditions-end
{
    // impl-start
    let q1 = s.take(i);
    let q2 = s.take(i + 1);
    assert(q2.last() == s[i]);
    assert(q2.drop_last() == q1);
    // impl-end
}
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

proof fn lemma_how_to_add_then_divide(x: int, y: int, d: int)
    // pre-conditions-start
    requires
        d > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        if_inner_lemma_how_to_add_then_divide(x, y, d),
    // post-conditions-end
{
    // impl-start
    lemma_fundamental_div_mod(x, d);
    lemma_fundamental_div_mod(y, d);
    lemma_mul_is_distributive_add(d, x / d, y / d);
    if (x % d) + (y % d) >= d {
        lemma_mul_is_distributive_add(d, (x / d) + (y / d), 1);
        lemma_fundamental_div_mod_converse(x + y, d, (x / d) + (y / d) + 1, (x % d) + (y % d) - d);
    } else {
        lemma_fundamental_div_mod_converse(x + y, d, (x / d) + (y / d), (x % d) + (y % d));
    }
    // impl-end
}
// pure-end

proof fn lemma_effect_of_dividing_by_two_or_more(x: int, d: int)
    // pre-conditions-start
    requires
        d >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        x > 0 ==> x / d < x,
        x < 0 ==> x / d < 0,
    // post-conditions-end
{
    // impl-start
    lemma_fundamental_div_mod(x, d);
    if x > 0 {
        lemma_div_is_ordered_by_denominator(x, 2, d);
    }
    // impl-end
}
// pure-end


spec fn expr_inner_divide_i32_by_u32(qr : (i32, u32), x: i32, d: u32) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end

fn divide_i32_by_u32(x: i32, d: u32) -> (qr: (i32, u32))
    // pre-conditions-start
    requires
        d > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        expr_inner_divide_i32_by_u32(qr, x, d),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

spec fn expr_inner_divide_i32_by_usize(qr : (i32, usize), x: i32, d: usize) -> (result:bool) {
    let (q, r) = qr;
    q == x as int / d as int && r == x as int % d as int
}
// pure-end

fn divide_i32_by_usize(x: i32, d: usize) -> (qr: (i32, usize))
    // pre-conditions-start
    requires
        d > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        expr_inner_divide_i32_by_usize(qr, x, d),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn compute_mean_of_i32s(numbers: &[i32]) -> (result: i32)
    // pre-conditions-start
    requires
        numbers.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == mean(numbers@.map(|_index, n: i32| n as int)),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn compute_absolute_difference(x: i32, y: i32) -> (z: u32)
    // post-conditions-start
    ensures
        z == abs(x - y),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn mean_absolute_deviation(numbers: &[i32]) -> (result: u32)
    // pre-conditions-start
    requires
        numbers.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == spec_mean_absolute_deviation(numbers@.map(|_index, n: i32| n as int)),
    // post-conditions-end
{
    return 0;  // TODO: Remove this line and implement the function body
}

}
fn main() {}
