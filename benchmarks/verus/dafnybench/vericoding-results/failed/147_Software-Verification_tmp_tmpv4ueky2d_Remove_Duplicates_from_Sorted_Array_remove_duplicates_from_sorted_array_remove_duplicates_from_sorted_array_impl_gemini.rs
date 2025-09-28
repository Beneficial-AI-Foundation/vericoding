// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
}

spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed forall proof syntax from 'implies' to 'ensures' */
proof fn lemma_sorted_distinct_last_is_ge(s: Seq<int>)
    requires
        is_sorted_and_distinct(s),
        s.len() > 0,
    ensures
        forall|i: int| 0 <= i < s.len() ==> s[i] <= s.last(),
{
    let last_idx = (s.len() - 1) as int;
    forall|i: int| 0 <= i < s.len()
        ensures s[i] <= s.last()
    {
        if i < last_idx {
            assert(s[i] < s[last_idx]);
        }
    }
}

/* helper modified by LLM (iteration 5): fixed forall proof syntax from 'implies' to 'ensures' */
proof fn lemma_push_preserves_sorted_distinct(s: Seq<int>, x: int)
    requires
        is_sorted_and_distinct(s),
        s.len() > 0,
        s.last() < x,
    ensures
        is_sorted_and_distinct(s.push(x)),
{
    lemma_sorted_distinct_last_is_ge(s);
    let s_new = s.push(x);
    forall|i: int, j: int| 0 <= i < j < s_new.len()
        ensures s_new[i] < s_new[j]
    {
        if j < s.len() {
            assert(s[i] < s[j]);
        } else {
            assert(j == s.len());
            assert(s[i] <= s.last());
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires 
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall|i: int| #![trigger nums[i]] 0 <= i < nums.len() ==> -100 <= nums[i] <= 100,
    ensures 
        is_sorted_and_distinct(result),
        forall|i: int| #![trigger nums.contains(i)] nums.contains(i) <==> result.contains(i),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): verified logic with fixed helpers */
{
    let mut result = Seq::new().push(nums[0]);
    let mut i: int = 1;
    while i < nums.len()
        invariant
            1 <= i <= nums.len(),
            is_sorted(nums),
            result.len() >= 1,
            is_sorted_and_distinct(result),
            result.last() <= nums[i-1],
            forall|x: int| nums.subrange(0, i).contains(x) <==> result.contains(x),
            forall|val: int| result.contains(val) ==> nums.contains(val),
        decreases nums.len() - i
    {
        if nums[i] > nums[i-1] {
            proof {
                assert(result.last() <= nums[i-1]);
                assert(nums[i-1] < nums[i]);
                assert(result.last() < nums[i]);
                
                // prove nums[i] is a new element for result
                assert forall |val: int| result.contains(val) implies val <= result.last() by {
                    lemma_sorted_distinct_last_is_ge(result);
                    assert(val <= result.last());
                }
                assert(!result.contains(nums[i]));

                // prove that the sets of elements remain equivalent
                let sub = nums.subrange(0, i);
                assert forall |x: int| sub.contains(x) <==> result.contains(x) by {}
                assert(!sub.contains(nums[i]));
            }
            lemma_push_preserves_sorted_distinct(result, nums[i]);
            result = result.push(nums[i]);
        }
        i = i + 1;
    }

    proof {
        let sub = nums.subrange(0, nums.len());
        assert(sub =~= nums);
        assert forall |x: int| nums.contains(x) <==> result.contains(x) by {}
    }
    
    result
}
// </vc-code>

}
fn main() {}