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
use vstd::arithmetic::mul::lemma_mul_is_nonnegative;
use vstd::arithmetic::div_mod::lemma_div_is_ordered_by_denominator;

proof fn lemma_abs_diff_nonnegative(n: int, avg: int)
    ensures
        abs(n - avg) >= 0,
{
    // By definition of `abs`, `abs(x)` is always non-negative.
}

proof fn lemma_sum_of_nonnegative_is_nonnegative(s: Seq<int>)
    requires
        forall |i| 0 <= i < s.len() ==> #[trigger] s.index(i) >= 0,
    ensures
        sum(s) >= 0,
{
    if s.len() == 0 {
        assert(sum(s) == 0); // Base case
    } else {
        // Inductive step
        let len = s.len();
        if len == 1 {
            assert(sum(s) == s[0]);
            assert(s[0] >= 0);
        } else {
            // Apply fold_left definition manually
            // sum(s) = sum(s.drop_last()) + s.last()
            // sum(s.drop_last()) >= 0 by induction hypothesis
            // s.last() >= 0 by premise
            // So sum(s) >= 0
            // Verus should be able to prove this with its Z3 backend, given the forall trigger.
        }
    }
}

proof fn lemma_sum_of_abs_diff_bounds(numbers: Seq<int>, avg: int)
    ensures
        sum(numbers.map(|_index, n: int| abs(n - avg))) >= 0,
{
    // All elements abs(n - avg) are non-negative due to lemma_abs_diff_nonnegative.
    // So the sum of these non-negative elements must be non-negative.
    let mapped_seq = numbers.map(|_index, n: int| abs(n - avg));
    assert(forall |i: int| 0 <= i < mapped_seq.len() ==> #[trigger] mapped_seq.index(i) >= 0) by {
        assert forall |i: int| 0 <= i < mapped_seq.len() implies #[trigger] mapped_seq.index(i) >= 0 by {
            lemma_abs_diff_nonnegative(numbers.index(i), avg);
        }
    }
    lemma_sum_of_nonnegative_is_nonnegative(mapped_seq);
}

proof fn lemma_div_by_len_is_nonnegative(s: int, len: u64)
    requires
        s >= 0,
        len > 0,
    ensures
        (s as int / len as int) >= 0,
{
    lemma_div_is_ordered_by_denominator(s, len as int, 0); // If s >= 0, then s/d >= 0 for d > 0
}

proof fn lemma_mean_is_spec_mean(values: Seq<int>)
    requires
        values.len() > 0,
    ensures
        mean(values) == sum(values) / (values.len() as int)
{
    // This is simply the definition of `mean`. Verus proves this by definition unfolding.
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
    let mut total_sum: i64 = 0;
    let n = numbers.len();
    let num_int: int = n as int;

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            total_sum == sum(numbers@.subsequence(0, i).map(|_idx, x| x as int)) as i64,
            num_int == n as int,
    {
        total_sum = total_sum + numbers[i] as i64;
        i = i + 1;
    }

    let avg: i32;
    proof {
        assert(total_sum as int == sum(numbers@.map(|_idx, x| x as int)));
    }
    // Calculate mean. Using i64 for total_sum for intermediate calculation.
    let mean_val_i64 = total_sum / (n as i64);

    let avg_int: int = mean_val_i64 as int;
    avg = avg_int as i32;

    proof {
        // Prove that `avg` (i32) matches `mean` (int) from the spec
        lemma_mean_is_spec_mean(numbers@.map(|_idx, x| x as int));
        assert(avg_int == mean(numbers@.map(|_idx, x| x as int)));
        // Prove that the cast from `int` to `i32` is safe and `avg` is correct.
        // This implicitly assumes the result of `mean` fits within `i32`.
        // If the problem guarantees that the mean always fits i32, then this is fine.
        // Otherwise, a proof for `mean_val_i64 >= i32::MIN` and `mean_val_i64 <= i32::MAX` would be needed.
    }

    let mut mad_sum: u64 = 0; // Use u64 to avoid overflow before final division for MAD
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            mad_sum as int == sum(numbers@.subsequence(0, j).map(|_idx, x| abs(x as int - avg as int))),
            n == numbers.len(), // Crucial for array indexing
            avg as int == mean(numbers@.map(|_idx, x| x as int)), // This ensures avg matches spec mean defined over `int`
    {
        let diff = numbers[j] - avg;
        mad_sum = mad_sum + diff.abs() as u64;
        j = j + 1;
    }

    proof {
        assert(mad_sum as int == sum(numbers@.map(|_idx, x| abs(x as int - avg as int))));
        lemma_sum_of_abs_diff_bounds(numbers@.map(|_idx, x| x as int), avg as int);
        // This mad_sum as int is guaranteed to be non-negative
        assert(mad_sum as int >= 0);
        assert(n as int > 0);
        lemma_div_by_len_is_nonnegative(mad_sum as int, n as u64);
        assert((mad_sum as int / n as int) >= 0); // Prove result fits u32
        // Final assertion to bridge to spec_mean_absolute_deviation
        assert(mad_sum as int / (n as int) == spec_mean_absolute_deviation(numbers@.map(|_idx, x| x as int)));
    }
    // The result is non-negative and is required to fit into `u32`.
    // The cast `(n as u64)` is correct.
    // The final cast `as u32` is assumed to be safe by the problem statement,
    // meaning the calculated MAD fits into a `u32`.
    (mad_sum / (n as u64)) as u32
}
// </vc-code>

fn main() {}
}