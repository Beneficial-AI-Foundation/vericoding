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
// <vc-helpers>
// <vc-helpers>

proof fn lemma_div_i64_matches_int(a: i64, b: usize)
    requires
        b > 0,
    ensures
        ((a / (b as i64)) as int) == (a as int) / (b as int),
        ((a % (b as i64)) as int) == (a as int) % (b as int),
{
    let bi: i64 = b as i64;
    let q: i64 = a / bi;
    let r: i64 = a % bi;
    // properties of machine integer division/modulo
    assert(a == q * bi + r);
    assert(0 <= r && r < bi);
    // cast to mathematical ints
    assert((a as int) == (q as int) * (bi as int) + (r as int));
    // apply the fundamental div/mod converse on mathematical ints
    proof {
        lemma_fundamental_div_mod_converse(a as int, bi as int, q as int, r as int);
    }
}

// </vc-helpers>
// </vc-helpers>
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
    let n: usize = numbers.len();

    // compute sum as i64 with invariant relating to spec sum
    let mut i: usize = 0usize;
    let mut sum_i64: i64 = 0i64;
    while i < n
        invariant i <= n;
        invariant (sum_i64 as int) == sum(numbers@.map(|idx, v: i32| if idx < i { v as int } else { 0 }));
    {
        sum_i64 = sum_i64 + (numbers[i] as i64);
        i = i + 1;
    }

    // average as i64
    let avg_i64: i64 = sum_i64 / (n as i64);

    // compute sum of absolute deviations as i64 with invariant relating to spec sum of abs
    let mut j: usize = 0usize;
    let mut sum_abs_i64: i64 = 0i64;
    while j < n
        invariant j <= n;
        invariant (sum_abs_i64 as int) ==
            sum(numbers@.map(|idx, v: i32| if idx < j { abs((v as int) - (avg_i64 as int)) } else { 0 }));
    {
        let diff: i64 = (numbers[j] as i64) - avg_i64;
        let ad: i64 = if diff >= 0 { diff } else { -diff };
        sum_abs_i64 = sum_abs_i64 + ad;
        j = j + 1;
    }

    // final result
    let res_u32: u32 = (sum_abs_i64 / (n as i64)) as u32;

    // proofs tying executable computation to the specification
    proof {
        // sum_i64 corresponds to spec sum
        assert((sum_i64 as int) == sum(numbers@.map(|_, v: i32| v as int)));

        // avg_i64 corresponds to spec mean
        lemma_div_i64_matches_int(sum_i64, n);
        assert((avg_i64 as int) == mean(numbers@.map(|_, v: i32| v as int)));

        // sum_abs_i64 corresponds to spec sum of absolute deviations from avg
        assert((sum_abs_i64 as int) ==
               sum(numbers@.map(|_, v: i32| abs((v as int) - (avg_i64 as int)))));

        // final division corresponds to spec division
        lemma_div_i64_matches_int(sum_abs_i64, n);
        assert(((sum_abs_i64 / (n as i64)) as int) ==
               spec_mean_absolute_deviation(numbers@.map(|_, v: i32| v as int)));
        assert((res_u32 as int) ==
               spec_mean_absolute_deviation(numbers@.map(|_, v: i32| v as int)));
    }

    res_u32
    // impl-end
}
// </vc-code>

fn main() {}
}