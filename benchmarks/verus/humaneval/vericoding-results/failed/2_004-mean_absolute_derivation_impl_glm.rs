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
proof fn sum_fold_left_commutative(seq1: Seq<int>, seq2: Seq<int>)
    ensures sum(seq1 + seq2) == sum(seq1) + sum(seq2)
{
    if seq1.len() == 0 {
        assert(sum(seq1 + seq2) == sum(seq2));
        assert(sum(seq1) + sum(seq2) == 0 + sum(seq2));
    } else {
        let last = seq1[seq1.len() - 1];
        let init = seq1.drop_last();
        assert(sum(seq1 + seq2) == sum(init + seq2.push_back(last)));
        assert(sum(init + seq2.push_back(last)) == sum(init + seq2) + last);
        sum_fold_left_commutative(init, seq2);
        assert(sum(init + seq2) == sum(init) + sum(seq2));
    }
}

proof fn mean_absolute_deviation_lemma(numbers: Seq<int>)
    requires
        numbers.len() > 0,
    ensures
        spec_mean_absolute_deviation(numbers) == sum(numbers.map(|_index, n: int| abs(n - mean(numbers)))) / (numbers.len() as int)
{
    reveal(sum);
    reveal(mean);
    reveal(abs);
}

/* helper modified by LLM (iteration 5): fixed missing comma in function parameters */
proof fn sum_map_composition<T, U, V>(seq: Seq<T>, f: spec fn(T) -> U, g: spec fn(U) -> V)
    ensures seq.map(|i, x| g(f(x))) == seq.map(|i, x| f(x)).map(|i, y| g(y))
{
    assert(seq.map(|i, x| g(f(x))) =~= seq.map(|i, x| f(x)).map(|i, y| g(y)));
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
/* code modified by LLM (iteration 5): implemented mean absolute deviation calculation */
{
    let len = numbers.len();
    
    // Calculate sum
    let mut total = 0i64;
    for i in 0..len {
        total += numbers[i] as i64;
    }
    
    // Calculate mean
    let average = total / len as i64;
    
    // Calculate mean absolute deviation
    let mut sum_deviations = 0i64;
    for i in 0..len {
        let deviation = if numbers[i] as i64 >= average {
            numbers[i] as i64 - average
        } else {
            average - numbers[i] as i64
        };
        sum_deviations += deviation;
    }
    
    let result = (sum_deviations / len as i64) as u32;
    result
}
// </vc-code>

}
fn main() {}