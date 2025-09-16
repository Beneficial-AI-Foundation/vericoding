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
/* helper modified by LLM (iteration 5): prefix sum for Seq<i32> */
spec fn prefix_sum_i32(numbers: Seq<i32>, len: nat) -> int {
    if len == 0 {
        0
    } else {
        prefix_sum_i32(numbers, len - 1) + (numbers@[len - 1] as int)
    }
}
/* helper modified by LLM (iteration 5): prefix sum of absolute differences to avg for Seq<i32> */
spec fn prefix_abs_diff_sum_i32(numbers: Seq<i32>, len: nat, avg: int) -> int {
    if len == 0 {
        0
    } else {
        prefix_abs_diff_sum_i32(numbers, len - 1, avg) + abs(numbers@[len - 1] as int - avg)
    }
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
    /* code modified by LLM (iteration 5): compute mean absolute deviation using prefix helpers and prove spec equivalence */
    let n: usize = numbers.len();

    let mut i: usize = 0;
    let mut s: i64 = 0;
    while i < n
        invariant
            s as int == prefix_sum_i32(numbers@, i as nat),
        decreases n - i
    {
        s = s + (numbers[i] as i64);
        i = i + 1;
    }

    let avg: i64 = s / (n as i64);
    let ghost avg_int: int = (s as int) / (n as int);

    let mut j: usize = 0;
    let mut sum_abs: i64 = 0;
    while j < n
        invariant
            sum_abs as int == prefix_abs_diff_sum_i32(numbers@, j as nat, avg_int),
        decreases n - j
    {
        let diff: i64 = (numbers[j] as i64) - avg;
        let absd: i64 = if diff >= 0 { diff } else { -diff };
        sum_abs = sum_abs + absd;
        j = j + 1;
    }

    let res_i64: i64 = sum_abs / (n as i64);
    let result: u32 = res_i64 as u32;

    proof {
        assert(s as int == prefix_sum_i32(numbers@, n as nat));
        assert(avg_int == prefix_sum_i32(numbers@, n as nat) / (n as int));
        assert(sum_abs as int == prefix_abs_diff_sum_i32(numbers@, n as nat, avg_int));
        assert(res_i64 as int == (sum_abs as int) / (n as int));
        assert(result as int == res_i64 as int);
        assert(result as int == spec_mean_absolute_deviation(numbers@.map(|_index, x: i32| x as int)));
    }

    result
}
// </vc-code>

}
fn main() {}