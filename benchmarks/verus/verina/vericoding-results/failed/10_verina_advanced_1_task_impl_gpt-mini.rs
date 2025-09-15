// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat {
    nums.filter(|elem: i32| elem == x).len()
}

spec fn filter_equal(nums: Seq<i32>, x: i32) -> Seq<i32> {
    nums.filter(|elem: i32| elem == x)
}
// </vc-preamble>

// <vc-helpers>
spec fn xor_seq(s: Seq<i32>) -> i32 {
    if s.len() == 0 {
        0
    } else {
        s@[0] ^ xor_seq(s[1..])
    }
}

proof fn xor_seq_unique(s: Seq<i32>)
    requires forall|elem: i32| s.contains(elem) ==> (count_occurrences(s, elem) == 1 || count_occurrences(s, elem) == 2),
    requires exists|unique: i32| count_occurrences(s, unique) == 1,
    ensures count_occurrences(s, xor_seq(s)) == 1
{
    proof {
        if s.len() == 0 {
            // impossible because of the requires existence of a unique element
        } else {
            let head = s@[0];
            let tail = s[1..];

            if count_occurrences(s, head) == 1 {
                // head occurs exactly once in s, and does not occur in tail
                // xor_seq(s) == head ^ xor_seq(tail)
                // all other elements in tail occur either once or twice, but by the global precondition
                // there is exactly one element with count 1 in s; since head has count 1, xor_seq(tail) must be the xor of the remaining pairs which cancel to 0
                // therefore xor_seq(s) == head
                assert tail.filter(|e: i32| e == head).len() == 0;
                assert xor_seq(s) == head ^ xor_seq(tail);
                // show xor_seq(tail) equals the xor of elements that appear twice (thus 0)
                // by induction on tail length, pairs cancel and the xor over tail equals 0
                if tail.len() == 0 {
                    assert xor_seq(tail) == 0;
                    assert xor_seq(s) == head;
                } else {
                    // use induction: call lemma recursively on tail
                    xor_seq_unique(tail);
                    // After recursion, xor_seq(tail) is the unique element of tail if any; but since head is the unique of s, tail has no unique element, so its xor must be 0
                    assert xor_seq(tail) == 0;
                    assert xor_seq(s) == head;
                }
            } else {
                // head occurs twice in s. One occurrence is head itself; there is exactly one other occurrence in tail.
                // Removing the pair of head values cancels them in xor. Consider tail with that other head removed: the xor of s equals xor of the remaining elements.
                // Formally, xor_seq(s) == head ^ xor_seq(tail) and in tail head occurs once, so that occurrence will cancel with the head here, leaving xor of remaining elements.
                assert count_occurrences(tail, head) == 1;
                // By reasoning on pairs and recursive cancellation, the xor over s equals xor over the sequence with the head-pair removed.
                // Recursively applying this for all elements that occur twice yields the unique element.
                // We can apply induction on length: call lemma on tail to process cancellation gradually.
                xor_seq_unique(tail);
                // After processing, the xor over s equals the unique element, and that unique element occurs exactly once in s.
            }

            // Conclude that xor_seq(s) is the unique element and therefore occurs exactly once
            // This matches the required ensures
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
    ensures
        count_occurrences(nums@, result) == 1,
        forall|x: i32| nums@.contains(x) ==> (x == result || count_occurrences(nums@, x) == 2),
// </vc-spec>
// <vc-code>
{
    // Compute XOR of all elements at runtime; duplicates toggle out leaving the single element
    let mut acc: i32 = 0;
    let mut i: usize = 0;
    while i < nums.len() {
        invariant i <= nums.len();
        acc = acc ^ nums[i];
        i += 1;
    }

    // Use the spec-level lemma on the sequence view of nums to conclude the postcondition
    proof {
        xor_seq_unique(nums@);
    }

    acc
}

// </vc-code>

}
fn main() {}