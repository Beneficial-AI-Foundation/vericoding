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
/* helper modified by LLM (iteration 5): added type annotations to closures and replaced Rust's .abs() with conditional expression for execution abs */
spec fn sum_i32_as_int(seq: Seq<i32>) -> int
{
    seq.map(|i, x| x as int).fold_left(0, |acc: int, x: int| acc + x)
}
spec fn sum_i64_spec(seq: Seq<i32>) -> i64
{
    seq.fold_left(0i64, |acc: i64, x: i32| acc + (x as i64))
}
proof fn lemma_sum_equiv(seq: Seq<i32>)
    ensures
        sum_i32_as_int(seq) == sum_i64_spec(seq) as int
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        let last = seq.last();
        let rest = seq.drop_last();
        lemma_sum_equiv(rest);
    }
}
spec fn sum_abs_int_spec(seq: Seq<int>, avg: int) -> int
{
    seq.fold_left(0, |acc: int, x: int| acc + abs(x - avg))
}
spec fn sum_abs_i64_spec(seq: Seq<i32>, avg: i64) -> i64
{
    seq.fold_left(0i64, |acc: i64, x: i32| acc + {
        let diff = x as i64 - avg;
        if diff < 0 { -diff } else { diff }
    })
}
proof fn lemma_sum_abs_equiv(seq: Seq<i32>, avg: i64)
    ensures
        sum_abs_i64_spec(seq, avg) as int == sum_abs_int_spec(seq.map(|i, x| x as int), avg as int)
    decreases seq.len()
{
    if seq.len() == 0 {
    } else {
        let last = seq.last();
        let rest = seq.drop_last();
        lemma_sum_abs_equiv(rest, avg);
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
    /* code modified by LLM (iteration 5): added type annotations to closures, replaced .abs() with conditional for execution abs, updated proof assertions */
    let n: usize = numbers.len();
    let sum_i64: i64 = numbers.iter().map(|x| *x as i64).sum();
    let avg_i64: i64 = sum_i64 / (n as i64);
    let mut sum_dev_i64: i64 = 0;
    for &num in numbers {
        let dev = num as i64 - avg_i64;
        sum_dev_i64 += if dev < 0 { -dev } else { dev };
    }
    let result: u32 = (sum_dev_i64 / (n as i64)) as u32;
    proof {
        let seq_i32 = numbers@;
        lemma_sum_equiv(seq_i32);
        let seq_int = seq_i32.map(|i, x| x as int);
        let s = sum(seq_int);
        assert(s == sum_i64 as int);
        let avg_int = mean(seq_int);
        assert(avg_int == avg_i64 as int);
        lemma_sum_abs_equiv(seq_i32, avg_i64);
        let sum_abs_exec = sum_abs_i64_spec(seq_i32, avg_i64);
        assert(sum_abs_exec as int == sum_abs_int_spec(seq_int, avg_int));
        assert(sum_abs_int_spec(seq_int, avg_int) == sum(seq_int.map(|i, x: int| abs(x - avg_int))));
        let total_dev_sum = sum(seq_int.map(|i, x: int| abs(x - avg_int)));
        assert(result as int == (sum_dev_i64 / (n as i64)) as int);
        assert(result as int == sum_dev_i64 as int / (n as int));
        assert(result as int == total_dev_sum / (n as int));
        assert(result as int == spec_mean_absolute_deviation(seq_int));
    }
    result
}
// </vc-code>

}
fn main() {}