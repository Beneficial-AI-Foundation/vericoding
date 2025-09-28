// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn first_digit(n: int) -> int
    recommends n > 0
    decreases n
{
    if n < 10 { n } else { first_digit(n / 10) }
}

spec fn last_digit(n: int) -> int
    recommends n > 0
{
    n % 10
}

spec fn is_odd(n: int) -> bool
{
    n == 1 || n == 3 || n == 5 || n == 7 || n == 9
}

spec fn satisfies_condition(n: int) -> bool
{
    n > 10 && is_odd(first_digit(n)) && is_odd(last_digit(n))
}

spec fn valid_input(nums: Seq<int>) -> bool
{
    true
}
spec fn count_helper(nums: Seq<int>, index: int) -> int
    recommends 0 <= index <= nums.len()
    decreases nums.len() - index when 0 <= index <= nums.len()
{
    if index == nums.len() {
        0
    } else {
        let current = nums[index];
        let contribution: int = if satisfies_condition(current) { 1 } else { 0 };
        contribution + count_helper(nums, index + 1)
    }
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed Set::<int>::empty() typing and strengthened proofs for base/inductive cases */
proof fn lemma_count_helper_properties(nums: Seq<int>, index: int)
    requires
        0 <= index,
        index <= nums.len(),
    ensures
        0 <= count_helper(nums, index),
        count_helper(nums, index) <= nums.len() - index,
        count_helper(nums, index) == Set::new(|i: int| index <= i < nums.len() && satisfies_condition(nums[i])).len(),
    decreases nums.len() - index
{
    if index == nums.len() {
        let S = Set::new(|i:int| index <= i < nums.len() && satisfies_condition(nums[i]));
        assert(count_helper(nums, index) == 0);
        assert forall|i:int| !S.contains(i) by {
            assert(index == nums.len());
            // If S.contains(i), then index <= i and i < nums.len() (= index), contradiction
            if index <= i && i < nums.len() {
                assert(i < index);
                assert(!(index <= i));
            }
        }
        assert forall|i:int| S.contains(i) == Set::<int>::empty().contains(i) by {
            assert(!S.contains(i));
            assert(!Set::<int>::empty().contains(i));
        }
        assert(S == Set::<int>::empty()) by {
            assert forall|i:int| S.contains(i) == Set::<int>::empty().contains(i) by { }
        }
        assert(S.len() == Set::<int>::empty().len());
        assert(Set::<int>::empty().len() == 0);
    } else {
        // Inductive step
        lemma_count_helper_properties(nums, index + 1);
        let cond = satisfies_condition(nums[index]);
        let c: int = if cond { 1 } else { 0 };
        let rest = count_helper(nums, index + 1);
        assert(count_helper(nums, index) == c + rest);
        assert(0 <= c);
        assert(c <= 1);
        assert(0 <= rest);
        assert(rest <= nums.len() - (index + 1));
        assert(0 <= c + rest);
        assert(c + rest <= nums.len() - index);

        let S0 = Set::new(|i:int| index <= i < nums.len() && satisfies_condition(nums[i]));
        let S1 = Set::new(|i:int| index + 1 <= i < nums.len() && satisfies_condition(nums[i]));

        if cond {
            let Single = Set::singleton(index);
            assert forall|i:int| S0.contains(i) == S1.union(Single).contains(i) by {
                // For i == index, S0.contains(i) is true (since cond), and Single.contains(i) is true
                if i == index {
                    assert(S1.contains(i) == false);
                    assert(Single.contains(i));
                } else {
                    // For i != index, membership coincides with S1
                    assert(Single.contains(i) == false);
                    assert(S0.contains(i) == S1.contains(i));
                }
            }
            assert(S0 == S1.union(Single)) by {
                assert forall|i:int| S0.contains(i) == S1.union(Single).contains(i) by { }
            }
            // Disjointness: no element of S1 equals index
            assert forall|i:int| !(S1.contains(i) && Single.contains(i)) by {
                if S1.contains(i) && Single.contains(i) {
                    assert(i >= index + 1);
                    assert(i == index);
                    assert(false);
                }
            }
            assert(S1.disjoint(Single)) by {
                assert forall|i:int| !(S1.contains(i) && Single.contains(i)) by { }
            }
            assert(Single.len() == 1);
            assert(S0.len() == S1.union(Single).len());
            assert(S1.union(Single).len() == S1.len() + Single.len());
            assert(S0.len() == 1 + S1.len());
            assert(count_helper(nums, index) == 1 + rest);
            assert(rest == S1.len());
            assert(count_helper(nums, index) == S0.len());
        } else {
            assert forall|i:int| S0.contains(i) == S1.contains(i) by { }
            assert(S0 == S1) by { assert forall|i:int| S0.contains(i) == S1.contains(i) by { } }
            assert(S0.len() == S1.len());
            assert(count_helper(nums, index) == rest);
            assert(rest == S1.len());
            assert(count_helper(nums, index) == S0.len());
        }
    }
}

/* helper modified by LLM (iteration 3): wrapper lemma specialized to index 0 with corrected typing */
proof fn lemma_count_helper_zero_index(nums: Seq<int>)
    ensures
        0 <= count_helper(nums, 0),
        count_helper(nums, 0) <= nums.len(),
        count_helper(nums, 0) == Set::new(|i:int| 0 <= i < nums.len() && satisfies_condition(nums[i])).len(),
{
    lemma_count_helper_properties(nums, 0);
}
// </vc-helpers>

// <vc-spec>
fn special_filter(nums: Seq<int>) -> (count: int)
    requires 
        valid_input(nums)
    ensures 
        count >= 0,
        count <= nums.len(),
        count == Set::new(|i: int| 0 <= i < nums.len() && satisfies_condition(nums[i])).len(),
        nums.len() == 0 ==> count == 0,
        forall|i: int| #![auto] 0 <= i < nums.len() && satisfies_condition(nums[i]) ==> 
            nums[i] > 10 && is_odd(first_digit(nums[i])) && is_odd(last_digit(nums[i]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): remove invalid int suffix and use helper lemma before returning count */
    proof { lemma_count_helper_zero_index(nums); }
    let count = count_helper(nums, 0);
    count
}
// </vc-code>


}

fn main() {}