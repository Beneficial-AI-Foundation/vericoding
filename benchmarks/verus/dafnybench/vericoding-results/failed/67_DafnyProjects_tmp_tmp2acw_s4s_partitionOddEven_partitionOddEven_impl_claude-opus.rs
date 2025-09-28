use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
// Helper lemma to show that swapping preserves multiset
proof fn swap_preserves_multiset(s: Seq<nat>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    // The multiset is preserved when we swap two elements
    let swapped = s.update(i, s[j]).update(j, s[i]);
    assert(swapped.to_multiset() =~= s.to_multiset());
}

// Executable versions of odd and even predicates
fn is_odd(n: nat) -> (result: bool)
    ensures result == odd(n)
{
    n % 2 == 1
}

fn is_even(n: nat) -> (result: bool)
    ensures result == even(n)
{
    n % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
// </vc-spec>
// <vc-code>
{
    let mut left: usize = 0;
    let mut right: usize = if a.len() > 0 { (a.len() - 1) as usize } else { 0 };
    
    while left < right
        invariant
            left <= right + 1,
            right < a@.len() || (a@.len() == 0 && right == 0),
            a@.to_multiset() == old(a)@.to_multiset(),
            // All elements before left are odd
            forall|i: int| 0 <= i < left ==> odd(a@[i]),
            // All elements after right are even
            forall|j: int| right < j < a@.len() ==> even(a@[j]),
    {
        // Find next even number from left
        while left <= right && is_odd(a[left])
            invariant
                left <= right + 1,
                right < a@.len() || (a@.len() == 0 && right == 0),
                a@.to_multiset() == old(a)@.to_multiset(),
                forall|i: int| 0 <= i < left ==> odd(a@[i]),
                forall|j: int| right < j < a@.len() ==> even(a@[j]),
        {
            left = left + 1;
        }
        
        // Find next odd number from right  
        while left < right && is_even(a[right])
            invariant
                left <= right,
                left < a@.len(),
                right < a@.len(),
                a@.to_multiset() == old(a)@.to_multiset(),
                even(a@[left as int]),
                forall|i: int| 0 <= i < left ==> odd(a@[i]),
                forall|j: int| right < j < a@.len() ==> even(a@[j]),
        {
            right = right - 1;
        }
        
        if left < right {
            // Swap a[left] and a[right]
            assert(even(a@[left as int]));
            assert(odd(a@[right as int]));
            
            let temp = a[left];
            let old_seq = a@;
            a.set(left, a[right]);
            let mid_seq = a@;
            assert(mid_seq =~= old_seq.update(left as int, old_seq[right as int]));
            a.set(right, temp);
            let new_seq = a@;
            assert(new_seq =~= mid_seq.update(right as int, temp as nat));
            assert(new_seq =~= old_seq.update(left as int, old_seq[right as int]).update(right as int, old_seq[left as int]));
            
            proof {
                swap_preserves_multiset(old_seq, left as int, right as int);
                assert(new_seq.to_multiset() =~= old_seq.to_multiset());
            }
            
            left = left + 1;
            right = right - 1;
        }
    }
    
    // Prove the postcondition
    assert forall|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) implies !odd(a@[j]) by {
        if i < left {
            // Elements before left are odd, so even(a@[i]) is false
            assert(odd(a@[i]));
            assert(false);
        } else if j > right {
            // Elements after right are even, so odd(a@[j]) is false
            assert(even(a@[j]));
            assert(!odd(a@[j]));
        } else {
            // i >= left and j <= right
            // If left > right, then i < j is impossible since i >= left > right >= j
            if left > right {
                assert(i >= left);
                assert(j <= right);
                assert(i > j);
                assert(false); // contradicts i < j
            }
            assert(!odd(a@[j]) || !even(a@[i]));
        }
    }
}
// </vc-code>

fn main() {}

}