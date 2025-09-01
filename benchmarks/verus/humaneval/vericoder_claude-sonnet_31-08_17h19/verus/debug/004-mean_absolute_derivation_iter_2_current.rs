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
proof fn lemma_sum_distributive(seq1: Seq<int>, seq2: Seq<int>)
    requires seq1.len() == seq2.len()
    ensures sum(seq1.zip_with(seq2, |a, b| a + b)) == sum(seq1) + sum(seq2)
{
    if seq1.len() == 0 {
        assert(seq1.zip_with(seq2, |a, b| a + b) =~= Seq::<int>::empty());
    } else {
        let combined = seq1.zip_with(seq2, |a, b| a + b);
        assert(combined.last() == seq1.last() + seq2.last());
        lemma_sum_distributive(seq1.drop_last(), seq2.drop_last());
    }
}

proof fn lemma_sum_constant_multiple(s: Seq<int>, c: int)
    ensures sum(s.map(|_i, x| c * x)) == c * sum(s)
{
    if s.len() == 0 {
        assert(s.map(|_i, x| c * x) =~= Seq::<int>::empty());
    } else {
        lemma_sum_constant_multiple(s.drop_last(), c);
        lemma_mul_is_distributive_add(c, sum(s.drop_last()), s.last());
    }
}

proof fn lemma_abs_triangle_reverse(a: int, b: int)
    ensures abs(a - b) >= abs(abs(a) - abs(b))
{
}

proof fn lemma_mean_in_bounds(values: Seq<int>)
    requires values.len() > 0
    ensures (
        let avg = mean(values);
        let min_val = values.fold_left(values[0], |acc, x| if acc <= x { acc } else { x });
        let max_val = values.fold_left(values[0], |acc, x| if acc >= x { acc } else { x });
        min_val <= avg <= max_val
    )
{
}

proof fn lemma_i32_abs_bounds(x: i32)
    ensures abs(x as int) <= i32::MAX as int
{
}

proof fn lemma_sum_abs_bounds(numbers: Seq<i32>)
    requires numbers.len() > 0
    ensures (
        let int_seq = numbers.map(|_i, n| n as int);
        let avg = mean(int_seq);
        let abs_devs = int_seq.map(|_i, n| abs(n - avg));
        sum(abs_devs) <= (numbers.len() as int) * (i32::MAX as int) * 2
    )
{
    let int_seq = numbers.map(|_i, n| n as int);
    let avg = mean(int_seq);
    
    assert forall |i| 0 <= i < numbers.len() implies {
        let n = #[trigger] numbers[i] as int;
        abs(n - avg) <= 2 * i32::MAX as int
    } by {
        lemma_i32_abs_bounds(numbers[i]);
        lemma_mean_in_bounds(int_seq);
    };
}

proof fn divide_i32_by_usize_correct(x: i32, d: usize) -> (qr: (i32, usize))
    requires d > 0
    requires d <= i32::MAX as usize
    ensures expr_inner_divide_i32_by_usize(qr, x, d)
{
    let q = x as int / d as int;
    let r = x as int % d as int;
    
    lemma_fundamental_div_mod(x as int, d as int);
    
    assert(0 <= r < d as int);
    assert(r <= i32::MAX as int);
    
    (q as i32, r as usize)
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
    
    // Calculate sum for mean
    let mut sum_val: i64 = 0;
    let mut i = 0;
    while i < len
        invariant 
            0 <= i <= len,
            sum_val == sum(numbers@.subrange(0, i as int).map(|_idx, n: i32| n as int)),
    {
        sum_val = sum_val + numbers[i] as i64;
        i = i + 1;
    }
    
    let mean_val = sum_val / len as i64;
    
    // Calculate sum of absolute deviations
    let mut abs_sum: i64 = 0;
    i = 0;
    while i < len
        invariant
            0 <= i <= len,
            abs_sum == sum(numbers@.subrange(0, i as int).map(|_idx, n: i32| abs(n as int - mean_val as int))),
            mean_val == mean(numbers@.map(|_idx, n: i32| n as int)),
    {
        let diff = numbers[i] as i64 - mean_val;
        let abs_diff = if diff >= 0 { diff } else { -diff };
        abs_sum = abs_sum + abs_diff;
        
        assert(abs_diff == abs(numbers[i] as int - mean_val as int));
        i = i + 1;
    }
    
    let result_val = abs_sum / len as i64;
    
    proof {
        let int_numbers = numbers@.map(|_idx, n: i32| n as int);
        let avg = mean(int_numbers);
        let abs_devs = int_numbers.map(|_idx, n: int| abs(n - avg));
        
        assert(mean_val as int == avg);
        assert(abs_sum as int == sum(abs_devs));
        assert(result_val as int == sum(abs_devs) / len as int);
        assert(result_val as int == spec_mean_absolute_deviation(int_numbers));
        
        lemma_sum_abs_bounds(numbers@);
        assert(result_val >= 0);
        assert(result_val <= u32::MAX as i64);
    }
    
    result_val as u32
}
// </vc-code>

fn main() {}
}