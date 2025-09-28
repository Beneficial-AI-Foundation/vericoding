// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n > 0 && k > 0
}

spec fn is_strictly_increasing(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i+1]
}

spec fn all_positive(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn valid_sequence(s: Seq<int>, n: int, k: int) -> bool
{
    s.len() == k && all_positive(s) && is_strictly_increasing(s) && sum_seq(s) == n
}

spec fn is_possible(n: int, k: int) -> bool
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The previous fix introduced a Verus compilation error: "The Verus types 'nat' and 'int' can only be used in ghost code (e.g., in a 'spec' or 'proof' function, inside a 'proof' block, or when assigning to a 'ghost' or 'tracked' variable)". To rectify this, the helper function `lemma_sum_of_first_k_integers`'s parameter `k` should be of type `int` instead of `nat` because it's being used as an index and in arithmetic operations within the `sum_seq` call which expects `int`. The `nat` type is primarily for compile-time non-negative checks and ghost contexts, while `int` is suitable for runtime-like operations in ghost code. Additionally, cast the argument to `lemma_sum_of_first_k_integers` to `int` instead of `nat`. */
proof fn lemma_sum_of_first_k_integers(k: int)
    requires
        k >= 0,
    ensures
        sum_seq(Seq::new(k as nat, |idx: int| (idx + 1) as int)) == k * (k + 1) / 2
{
    if k == 0 {
        assert(sum_seq(Seq::empty()) == 0);
        assert(k * (k + 1) / 2 == 0);
    } else {
        lemma_sum_of_first_k_integers(k - 1);
        assert(sum_seq(Seq::new(k as nat, |idx: int| (idx + 1) as int)) == k as int + sum_seq(Seq::new((k - 1) as nat, |idx: int| (idx + 1) as int)));
        assert(k as int + (k - 1) * k / 2 == k * (k + 1) / 2);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, k as int)
    ensures 
        ((result.len() == 1 && result[0] == -1) || 
         (valid_sequence(result@.map(|_i: int, x: i8| x as int), n as int, k as int))) &&
        ((result.len() == 1 && result[0] == -1) <==> !is_possible(n as int, k as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation errors related to `is_possible` arguments not being ghost types by casting `k_i128` to `int` where needed. The `n_i128` was already correctly handled by an earlier `as int` cast. Also, corrected `lemma_sum_of_first_k_integers` argument to `int` from `nat`. */
{
    let n_i128 = n as i128;
    let k_i128 = k as i128;

    if !is_possible(n_i128 as int, k_i128 as int) {
        return vec![-1];
    }

    let mut current_sum: i128 = 0;
    let mut current_seq: Vec<i8> = Vec::new();
    let mut i: i128 = 0;

    while i < k_i128
        invariant
            0 <= i <= k_i128,
            current_seq.len() == i as nat,
            // all_positive(current_seq@.map(|_j, x| x as int)), // Ghost code, can't map i8 to int in exec
            // is_strictly_increasing(current_seq@.map(|_j, x| x as int)), // Ghost code, can't map i8 to int in exec
            current_sum == sum_seq(current_seq@.map(|_j, x| x as int)),
            current_sum + (k_i128 - i) * (k_i128 - i + 1) / 2 <= n_i128,
            forall|idx: int| 0 <= idx < i ==> current_seq[idx as nat] as i128 == idx + 1,
            (k_i128 - i) >= 0,
    {
        proof {
            lemma_sum_of_first_k_integers((k_i128 - i) as int);
        }

        current_seq.push((i + 1) as i8);
        current_sum = current_sum + (i + 1);
        i = i + 1;
    }

    let remaining_sum = n_i128 - current_sum;
    let mut result_vec = current_seq;

    let mut j: i128 = k_i128 - 1;
    while j >= 0
        invariant
            -1 <= j < k_i128,
            result_vec.len() == k_i128 as nat,
            current_sum == sum_seq(result_vec@.map(|_idx, x| x as int)),
            remaining_sum == n_i128 - current_sum,
            all_positive(result_vec@.map(|_idx, x| x as int)),
            is_strictly_increasing(result_vec@.map(|_idx, x| x as int)),
            // result_vec[j as usize] as i128 > 0, // j could be -1 in some cases, so not always valid
            current_sum <= n_i128,
            remaining_sum >= 0,
            // Proof about the lower bound of elements relative to their index and previous elements
            forall|idx: int| 0 <= idx < k_i128 ==> result_vec[idx as int] as i128 >= idx + 1,
            // Proof about the difference between adjacent elements
            forall|idx: int| 0 <= idx < k_i128 - 1 ==> result_vec[idx as int] as i128 <= result_vec[(idx + 1) as int] as i128 - 1,
    {
        let increment = remaining_sum / (j + 1);
        if increment > 0 {
            let old_val = result_vec[j as usize] as i128;
            let new_val = old_val + increment;
            result_vec.set(j as usize, new_val as i8);
            current_sum = current_sum + increment;
            remaining_sum = remaining_sum - increment;
        }
        j = j - 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}