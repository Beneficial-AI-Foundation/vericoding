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
/* helper modified by LLM (iteration 5): Added missing helper functions */
proof fn lemma_sum_push(s: Seq<int>, x: int)
    ensures sum(s.push(x)) == sum(s) + x
{
    reveal(sum);
    assert(s.push(x).fold_left(0, |acc: int, y| acc + y) == s.fold_left(0, |acc: int, y| acc + y) + x);
}

fn divide_i32_by_usize(x: i32, d: usize) -> (result: (i32, usize))
    requires d > 0
    ensures expr_inner_divide_i32_by_usize(result, x, d)
{
    let q = x / (d as i32);
    let r = (x % (d as i32)) as usize;
    (q, r)
}

proof fn lemma_map_len<T, U>(s: Seq<T>, f: spec_fn(int, T) -> U)
    ensures s.map(f).len() == s.len()
{
    assert(s.map(f).len() == s.len());
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
/* code modified by LLM (iteration 5): Fixed function calls to use proper helper functions */
{
    let len = numbers.len();
    let mut sum_total: i32 = 0;
    let mut i: usize = 0;
    
    while i < len
        invariant
            0 <= i <= len,
            sum_total == sum(numbers@.map(|_index, n: i32| n as int).subrange(0, i as int)),
        decreases len - i
    {
        sum_total = sum_total + numbers[i];
        i = i + 1;
        proof {
            let s = numbers@.map(|_index, n: i32| n as int);
            assert(s.subrange(0, i as int) =~= s.subrange(0, (i - 1) as int).push(s[(i - 1) as int]));
            lemma_sum_push(s.subrange(0, (i - 1) as int), s[(i - 1) as int]);
        }
    }
    
    assert(numbers@.map(|_index, n: i32| n as int).subrange(0, len as int) =~= numbers@.map(|_index, n: i32| n as int));
    
    let (avg, _) = divide_i32_by_usize(sum_total, len);
    
    let mut sum_deviations: u32 = 0;
    let mut j: usize = 0;
    
    while j < len
        invariant
            0 <= j <= len,
            sum_deviations == sum(numbers@.map(|_index, n: i32| n as int).subrange(0, j as int).map(|_index, n: int| abs(n - avg as int))),
        decreases len - j
    {
        let diff = numbers[j] - avg;
        let abs_diff: u32 = if diff >= 0 { diff as u32 } else { (-diff) as u32 };
        sum_deviations = sum_deviations + abs_diff;
        j = j + 1;
        proof {
            let s = numbers@.map(|_index, n: i32| n as int);
            let mapped_j = s.subrange(0, j as int).map(|_index, n: int| abs(n - avg as int));
            let mapped_j_minus_1 = s.subrange(0, (j - 1) as int).map(|_index, n: int| abs(n - avg as int));
            assert(mapped_j =~= mapped_j_minus_1.push(abs(s[(j - 1) as int] - avg as int)));
            lemma_sum_push(mapped_j_minus_1, abs(s[(j - 1) as int] - avg as int));
        }
    }
    
    assert(numbers@.map(|_index, n: i32| n as int).subrange(0, len as int) =~= numbers@.map(|_index, n: i32| n as int));
    
    let result = (sum_deviations / len as u32) as u32;
    proof {
        lemma_map_len(numbers@.map(|_index, n: i32| n as int), |_index, n: int| abs(n - avg as int));
    }
    result
}
// </vc-code>

}
fn main() {}