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
// No additional helper functions required for this proof.
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
    let s = numbers@;
    let len = numbers.len();

    let mut i: usize = 0;
    let mut sum_acc: int = 0;
    while i < len
        invariant i <= len;
        invariant sum_acc == sum(s.slice(0, i).map(|_idx, x: i32| x as int));
    {
        let v = numbers[i];
        sum_acc = sum_acc + (v as int);
        i = i + 1;
    }

    let avg: int = sum_acc / (len as int);

    let mut j: usize = 0;
    let mut dev_sum: int = 0;
    while j < len
        invariant j <= len;
        invariant dev_sum == sum(s.slice(0, j).map(|_idx, x: i32| abs((x as int) - avg)));
        invariant dev_sum >= 0;
    {
        let v = numbers[j];
        let d: int = v as int - avg;
        let ad: int = if d >= 0 { d } else { -d };
        // relate the computed absolute value to the spec `abs`
        assert(ad == abs(d));
        dev_sum = dev_sum + ad;
        j = j + 1;
    }

    let result_int: int = dev_sum / (len as int);
    proof {
        // dev_sum corresponds to the sum of absolute deviations for the whole sequence
        assert(dev_sum == sum(s.map(|_idx, x: i32| abs((x as int) - avg))));
    }
    result_int as u32
}
// </vc-code>

fn main() {}
}