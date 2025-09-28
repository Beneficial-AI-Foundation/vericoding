// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat 
    decreases nums.len()
{
    if nums.len() == 0 {
        0
    } else {
        let first = nums[0];
        let rest_count = count_occurrences(nums.subrange(1, nums.len() as int), x);
        if first == x {
            rest_count + 1
        } else {
            rest_count
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): preserved lemmas; minor comment updates, no logic changes */
proof fn lemma_count_sum_two_leq_len(nums: Seq<i32>, a: i32, b: i32)
    requires
        a != b,
    ensures
        count_occurrences(nums, a) + count_occurrences(nums, b) <= nums.len(),
    decreases nums.len()
{
    reveal(count_occurrences);
    if nums.len() == 0 {
        // base case: both counts are 0
    } else {
        let n = nums.len();
        let rest = nums.subrange(1, n as int);
        lemma_count_sum_two_leq_len(rest, a, b);
        let first = nums[0];

        if first == a {
            assert(a != b);
            assert(first != b);
            assert(count_occurrences(nums, a) == count_occurrences(rest, a) + 1);
            assert(count_occurrences(nums, b) == count_occurrences(rest, b));
            let sum_rest = count_occurrences(rest, a) + count_occurrences(rest, b);
            assert(count_occurrences(nums, a) + count_occurrences(nums, b) == sum_rest + 1);
            assert(sum_rest <= rest.len());
            assert(sum_rest + 1 <= rest.len() + 1);
            assert(rest.len() + 1 == n);
        } else if first == b {
            assert(a != b);
            assert(first != a);
            assert(count_occurrences(nums, a) == count_occurrences(rest, a));
            assert(count_occurrences(nums, b) == count_occurrences(rest, b) + 1);
            let sum_rest = count_occurrences(rest, a) + count_occurrences(rest, b);
            assert(count_occurrences(nums, a) + count_occurrences(nums, b) == sum_rest + 1);
            assert(sum_rest <= rest.len());
            assert(sum_rest + 1 <= rest.len() + 1);
            assert(rest.len() + 1 == n);
        } else {
            assert(count_occurrences(nums, a) == count_occurrences(rest, a));
            assert(count_occurrences(nums, b) == count_occurrences(rest, b));
            let sum_rest = count_occurrences(rest, a) + count_occurrences(rest, b);
            assert(count_occurrences(nums, a) + count_occurrences(nums, b) == sum_rest);
            assert(sum_rest <= rest.len());
            assert(rest.len() + 1 == n);
            assert(rest.len() <= n);
        }
    }
}

/* helper modified by LLM (iteration 5): arithmetic tightening in majority bound lemma; logic unchanged */
proof fn lemma_bound_other(nums: Seq<i32>, r: i32, x: i32)
    requires
        x != r,
        count_occurrences(nums, r) > nums.len() / 2,
    ensures
        count_occurrences(nums, x) <= nums.len() / 2,
{
    lemma_count_sum_two_leq_len(nums, r, x);
    let a = count_occurrences(nums, x);
    let b = count_occurrences(nums, r);
    let n = nums.len();

    assert(a + b <= n);
    // From b > n/2 (nat), we can use discrete arithmetic to get b >= n/2 + 1
    assert(b >= n/2 + 1) by {
        assert(n/2 < b);
    };
    assert(a <= n - b);
    assert(n - b <= n - (n/2 + 1));
    assert(n - (n/2 + 1) <= n/2);
    assert(a <= n/2);
}

/* helper modified by LLM (iteration 5): keep forall-by proof; no logical changes */
proof fn lemma_no_other_exceeds_half(nums: Seq<i32>, r: i32)
    requires
        count_occurrences(nums, r) > nums.len() / 2,
    ensures
        forall|x: i32| x != r ==> count_occurrences(nums, x) <= nums.len() / 2,
{
    assert_forall_by(|x: i32| {
        if x != r {
            lemma_bound_other(nums, r, x);
            assert(count_occurrences(nums, x) <= nums.len() / 2);
        }
        assert(x != r ==> count_occurrences(nums, x) <= nums.len() / 2);
    });
}
// </vc-helpers>

// <vc-spec>
fn majority_element(nums: Seq<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|x: i32| count_occurrences(nums, x) > nums.len() / 2,
    ensures 
        count_occurrences(nums, result) > nums.len() / 2,
        forall|x: i32| x != result ==> count_occurrences(nums, x) <= nums.len() / 2,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix nat/int mismatch by casting 2 to nat in the choose predicate */
    let r = choose|x: i32| count_occurrences(nums, x) > nums.len() / (2 as nat);
    proof { lemma_no_other_exceeds_half(nums, r); }
    r
}
// </vc-code>

}
fn main() {}