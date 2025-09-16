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
/* helper modified by LLM (iteration 4): added conversion helpers between i32 and int */
spec fn i32_to_int(x: i32) -> int {
    x as int
}

spec fn int_to_i32(x: int) -> i32 {
    x as i32
}

/* helper modified by LLM (iteration 3): fixed syntax from 'proof lemma' to 'proof fn' */
proof fn abs_def(x: int)
    ensures abs(x) == (if x >= 0 { x } else { -x })
{
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
/* code modified by LLM (iteration 5): fixed range indexing in while loop invariants by converting i to int */
{
    let n = numbers.len() as i32;
    let mut total: i32 = 0;
    let mut i: usize = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            total as int == sum(numbers@[0..(i as int)].map(|_index, j: i32| j as int)),
    {
        total += numbers[i];
        i += 1;
    }
    
    let avg = total / n;
    
    let mut abs_dev_sum: i32 = 0;
    i = 0;
    while i < numbers.len()
        invariant
            0 <= i <= numbers.len(),
            abs_dev_sum as int == sum(numbers@[0..(i as int)].map(|_index, j: i32| abs((j as int) - (avg as int)))),
    {
        let num = numbers[i];
        let dev = if num >= avg { num - avg } else { avg - num };
        proof {
            abs_def(num as int - avg as int);
        }
        abs_dev_sum += dev;
        i += 1;
    }

    let mad = abs_dev_sum / n;
    mad as u32
}
// </vc-code>

}
fn main() {}