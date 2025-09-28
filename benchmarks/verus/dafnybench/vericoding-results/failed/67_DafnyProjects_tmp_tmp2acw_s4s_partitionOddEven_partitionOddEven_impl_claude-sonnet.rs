use vstd::prelude::*;

verus! {

// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

spec fn odd(n: nat) -> bool { n % 2 == 1 }
spec fn even(n: nat) -> bool { n % 2 == 0 }

// <vc-helpers>
spec fn all_odd_before_even(s: Seq<nat>) -> bool {
    !(exists|i: int, j: int| 0 <= i < s.len() && i < j && even(s[i]) && odd(s[j]))
}

spec fn is_partition_point(s: Seq<nat>, k: int) -> bool {
    0 <= k <= s.len() &&
    (forall|i: int| 0 <= i < k ==> odd(s[i])) &&
    (forall|i: int| k <= i < s.len() ==> even(s[i]))
}

spec fn swap_result(v: Seq<nat>, i: int, j: int) -> Seq<nat> {
    v.update(i, v[j]).update(j, v[i])
}

proof fn lemma_partition_point_implies_property(s: Seq<nat>, k: int)
    requires is_partition_point(s, k)
    ensures all_odd_before_even(s)
{
    if exists|i: int, j: int| 0 <= i < s.len() && i < j && even(s[i]) && odd(s[j]) {
        let i = choose|i: int| exists|j: int| 0 <= i < s.len() && i < j && even(s[i]) && odd(s[j]);
        let j = choose|j: int| 0 <= i < s.len() && i < j && even(s[i]) && odd(s[j]);
        
        if i < k {
            assert(odd(s[i]));
            assert(even(s[i]));
            assert(false);
        } else {
            assert(even(s[i]));
        }
        
        if j < k {
            assert(odd(s[j]));
        } else {
            assert(even(s[j]));
            assert(odd(s[j]));
            assert(false);
        }
    }
}

proof fn lemma_swap_preserves_multiset(v: Vec<nat>, i: usize, j: usize)
    requires i < v.len(), j < v.len()
    ensures swap_result(v@, i as int, j as int).to_multiset() == v@.to_multiset()
{
    assert(v@.update(i as int, v@[j as int]).update(j as int, v@[i as int]).to_multiset() == v@.to_multiset());
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
    let mut right: usize = a.len();
    
    while left < right
        invariant
            left <= right,
            right <= a.len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> odd(a@[i]),
            forall|i: int| right <= i < a.len() ==> even(a@[i]),
    {
        if odd(a[left]) {
            left = left + 1;
        } else {
            assert(even(a[left]));
            right = right - 1;
            
            proof {
                lemma_swap_preserves_multiset(*a, left, right);
            }
            
            let temp = a[left];
            a.set(left, a[right]);
            a.set(right, temp);
        }
    }
    
    proof {
        assert(left == right);
        assert(is_partition_point(a@, left as int));
        lemma_partition_point_implies_property(a@, left as int);
    }
}
// </vc-code>

fn main() {}

}