use vstd::calc;
use vstd::prelude::*;
use vstd::seq_lib::lemma_multiset_commutative;

verus! {

// <vc-helpers>
// Helper function to find the index of the minimum element in a sequence
spec fn find_min_index(s: Seq<i32>) -> nat
    recommends s.len() > 0
{
    choose |i: nat| i < s.len() && forall |j: nat| j < s.len() ==> s[i as int] <= s[j as int]
}

// Helper function to find the index of the maximum element in a sequence
spec fn find_max_index(s: Seq<i32>) -> nat
    recommends s.len() > 0
{
    choose |i: nat| i < s.len() && forall |j: nat| j < s.len() ==> s[i as int] >= s[j as int]
}

// Helper to remove an element at a given index from a sequence
spec fn remove_at(s: Seq<i32>, idx: nat) -> Seq<i32>
    recommends idx < s.len()
{
    s.subrange(0, idx as int) + s.subrange(idx as int + 1, s.len() as int)
}

proof fn lemma_remove_at_len(s: Seq<i32>, idx: nat)
    requires idx < s.len()
    ensures remove_at(s, idx).len() == s.len() - 1
{
    assert(remove_at(s, idx) =~= s.subrange(0, idx as int) + s.subrange(idx as int + 1, s.len() as int));
}
// </vc-helpers>

// <vc-spec>
fn strange_sort_list(s: &Vec<i32>) -> (ret: Vec<i32>)
    // post-conditions-start
    ensures
        s@.len() == ret@.len(),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut remaining: Vec<i32> = Vec::new();
    
    // Copy input to remaining
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            remaining@.len() == i,
            forall |j: nat| j < i ==> remaining@[j as int] == s@[j as int],
    {
        remaining.push(s[i]);
        i = i + 1;
    }
    
    let mut take_min = true;
    
    while remaining.len() > 0
        invariant
            result@.len() + remaining@.len() == s@.len(),
    {
        if remaining.len() == 1 {
            result.push(remaining[0]);
            remaining = Vec::new();
        } else {
            // Find min or max
            let mut target_idx = 0;
            let mut j = 1;
            
            if take_min {
                // Find minimum
                while j < remaining.len()
                    invariant
                        1 <= j <= remaining.len(),
                        0 <= target_idx < remaining.len(),
                        forall |k: nat| k < j ==> remaining@[target_idx as int] <= remaining@[k as int],
                {
                    if remaining[j] < remaining[target_idx] {
                        target_idx = j;
                    }
                    j = j + 1;
                }
            } else {
                // Find maximum
                while j < remaining.len()
                    invariant
                        1 <= j <= remaining.len(),
                        0 <= target_idx < remaining.len(),
                        forall |k: nat| k < j ==> remaining@[target_idx as int] >= remaining@[k as int],
                {
                    if remaining[j] > remaining[target_idx] {
                        target_idx = j;
                    }
                    j = j + 1;
                }
            }
            
            // Add the element to result
            result.push(remaining[target_idx]);
            
            // Remove element from remaining by building new vector
            let mut new_remaining: Vec<i32> = Vec::new();
            let mut k = 0;
            while k < remaining.len()
                invariant
                    0 <= k <= remaining.len(),
                    0 <= target_idx < remaining.len(),
                    new_remaining@.len() == if k <= target_idx { k as nat } else { (k - 1) as nat },
                    forall |m: nat| m < new_remaining@.len() ==> {
                        if m < target_idx {
                            new_remaining@[m as int] == remaining@[m as int]
                        } else {
                            new_remaining@[m as int] == remaining@[(m + 1) as int]
                        }
                    },
            {
                if k != target_idx {
                    new_remaining.push(remaining[k]);
                }
                k = k + 1;
            }
            
            remaining = new_remaining;
            take_min = !take_min;
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}