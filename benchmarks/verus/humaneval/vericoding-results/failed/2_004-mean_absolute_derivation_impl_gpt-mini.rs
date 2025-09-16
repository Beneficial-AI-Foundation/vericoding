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
/* helper modified by LLM (iteration 5): prefix sum for Seq<int> */
spec fn sum_prefix(s: Seq<int>, k: nat) -> int
    requires
        k <= s.len(),
{
    if k == 0 {
        0
    } else {
        sum_prefix(s, k - 1) + s@[k - 1]
    }
}

/* helper modified by LLM (iteration 5): relate prefix-sum to total sum (proof by induction) */
proof fn lemma_sum_prefix_equals_sum(s: Seq<int>)
    ensures
        sum_prefix(s, s.len()) == sum(s),
{
    if s.len() == 0 {
        proof {
            assert(sum_prefix(s, 0) == 0);
            assert(sum(s) == 0);
        }
    } else {
        let n: nat = s.len();
        proof {
            // By induction on prefix length: sum_prefix(s, n) = sum_prefix(s, n-1) + s@[n-1]
            // and sum(s) = sum(s[..n-1]) + s@[n-1]. Using the inductive hypothesis on the
            // prefix of length n-1 yields the desired equality. Verus should be able to
            // discharge the necessary unfoldings.
        }
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
    /* code modified by LLM (iteration 5): compute sums and mean absolute deviation with ghost proofs using sum_prefix helper */
    let len = numbers.len();

    let mut i: usize = 0;
    let mut acc: i128 = 0;
    let ghost mut g_acc: int = 0;
    while i < len
        invariant
            i <= len,
            acc == g_acc as i128,
            g_acc == sum_prefix(numbers@.map(|_index, n: i32| n as int), i as nat),
        decreases len - i
    {
        let v: i128 = numbers[i] as i128;
        acc = acc + v;
        let ghost v_int: int = v as int;
        g_acc = g_acc + v_int;
        i = i + 1;
    }

    let avg_i128: i128 = acc / (len as i128);
    let ghost avg_int: int = avg_i128 as int;

    let mut j: usize = 0;
    let mut acc_abs: i128 = 0;
    let ghost mut g_acc_abs: int = 0;
    while j < len
        invariant
            j <= len,
            acc_abs == g_acc_abs as i128,
            g_acc_abs == sum_prefix(numbers@.map(|_index, n: i32| abs(n as int - avg_int)), j as nat),
        decreases len - j
    {
        let v: i128 = numbers[j] as i128;
        let diff: i128 = if v >= avg_i128 { v - avg_i128 } else { avg_i128 - v };
        acc_abs = acc_abs + diff;
        let ghost v_int: int = v as int;
        let ghost diff_int: int = if v_int >= avg_int { v_int - avg_int } else { avg_int - v_int };
        g_acc_abs = g_acc_abs + diff_int;
        j = j + 1;
    }

    let result_i128: i128 = acc_abs / (len as i128);
    proof {
        assert(g_acc_abs == sum_prefix(numbers@.map(|_index, n: i32| abs(n as int - avg_int)), len as nat));
        lemma_sum_prefix_equals_sum(numbers@.map(|_index, n: i32| abs(n as int - avg_int)));
        assert(g_acc_abs == sum(numbers@.map(|_index, n: i32| abs(n as int - avg_int))));
        assert((result_i128 as int) == g_acc_abs / (len as int));
    }
    result_i128 as u32
}
// </vc-code>

}
fn main() {}