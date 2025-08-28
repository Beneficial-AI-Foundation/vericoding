use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
spec fn count_odds(s: Seq<nat>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if odd(s[0]) { 1 } else { 0 }) + count_odds(s.drop_first())
    }
}

spec fn all_odds_before_evens(s: Seq<nat>) -> bool {
    !exists|i: int, j: int| 0 <= i < j < s.len() && even(s[i]) && odd(s[j])
}

proof fn lemma_swap_preserves_multiset(v: Seq<nat>, i: int, j: int)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
    ensures
        v.swap(i, j).to_multiset() == v.to_multiset(),
{
    assert(v.swap(i, j).to_multiset() == v.to_multiset());
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn partitionOddEven(a: &mut Vec<nat>)
    ensures 
        a@.to_multiset() == old(a)@.to_multiset(),
        !(exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j])),
// </vc-spec>
// </vc-spec>

// <vc-code>
fn partition_odd_even(a: &mut Vec<nat>)
    ensures
        a@.to_multiset() == old(a)@.to_multiset(),
        !exists|i: int, j: int| 0 <= i < j < a@.len() && even(a@[i]) && odd(a@[j]),
{
    let mut i: usize = 0;
    let mut j: usize = if a.len() > 0 { a.len() - 1 } else { 0 };
    
    while i < j
        invariant
            0 <= i <= a@.len(),
            0 <= j <= a@.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|k: int| 0 <= k < i ==> odd(a@[k]),
            forall|k: int| j < k < a@.len() ==> even(a@[k]),
        decreases a@.len() - i
    {
        if odd(a[i]) {
            i = i + 1;
        } else {
            while i < j && even(a[j])
                invariant
                    0 <= i <= a@.len(),
                    0 <= j <= a@.len(),
                    a@.to_multiset() == old(a)@.to_multiset(),
                    forall|k: int| 0 <= k < i ==> odd(a@[k]),
                    forall|k: int| j <= k < a@.len() ==> even(a@[k]),
                decreases j
            {
                if j > 0 {
                    j = j - 1;
                } else {
                    break;
                }
            }
            if i < j {
                a.swap(i, j);
                lemma_swap_preserves_multiset(a@, i as int, j as int);
                i = i + 1;
            }
        }
    }
}
// </vc-code>

fn main() {}

}