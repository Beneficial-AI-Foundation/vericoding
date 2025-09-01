use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_multiset_swap<T>(s: Seq<T>, i: int, j: int)
    requires
        0 <= i < s.len(),
        0 <= j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() == s.to_multiset(),
{
    let s1 = s.update(i, s[j]);
    let s2 = s1.update(j, s[i]);
    
    assert(s2.to_multiset().count(s[i]) == s.to_multiset().count(s[i]));
    assert(s2.to_multiset().count(s[j]) == s.to_multiset().count(s[j]));
    
    assert forall|x: T| s2.to_multiset().count(x) == s.to_multiset().count(x) by {
        if x == s[i] && x == s[j] {
            // same element, count unchanged
        } else if x == s[i] {
            // x appears at position j in s2, was at position i in s
        } else if x == s[j] {
            // x appears at position i in s2, was at position j in s
        } else {
            // x unchanged at all other positions
        }
    }
}

proof fn lemma_sorted_after_swap(a: &Vec<bool>, left: usize, right: usize)
    requires
        left < a.len(),
        right < a.len(),
        left < right,
        a@[left as int] == true,
        a@[right as int] == false,
        forall|i: int, j: int| 0 <= i < j < a.len() && (i != left || j != right) ==> !a@[i] || a@[j],
    ensures
        ({
            let new_a = a@.update(left as int, false).update(right as int, true);
            forall|i: int, j: int| 0 <= i < j < new_a.len() ==> !new_a[i] || new_a[j]
        })
{
    let new_a = a@.update(left as int, false).update(right as int, true);
    
    assert forall|i: int, j: int| 0 <= i < j < new_a.len() implies !new_a[i] || new_a[j] by {
        if i == left && j == right {
            assert(!new_a[i]);
        } else if i == left {
            assert(!new_a[i]);
        } else if j == right {
            assert(new_a[j]);
        } else {
            assert(!a@[i] || a@[j]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn two_way_sort(a: &mut Vec<bool>)
    // pre-conditions-start
    requires
        old(a).len() <= 100_000,
    // pre-conditions-end
    // post-conditions-start
    ensures
        a.len() == old(a).len(),
        a@.to_multiset() == old(a)@.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> !a[i] || a[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut left: usize = 0;
    let mut right: usize = if a.len() == 0 { 0 } else { a.len() - 1 };
    
    while left < right
        invariant
            left <= a.len(),
            right < a.len(),
            a.len() == old(a).len(),
            a@.to_multiset() == old(a)@.to_multiset(),
            forall|i: int| 0 <= i < left ==> !a@[i],
            forall|i: int| right < i < a.len() ==> a@[i],
            forall|i: int, j: int| 0 <= i < j < a.len() && (j <= left || right <= i) ==> !a@[i] || a@[j],
        decreases right - left
    {
        if !a[left] {
            left += 1;
        } else if a[right] {
            right -= 1;
        } else {
            proof {
                lemma_multiset_swap(a@, left as int, right as int);
            }
            
            let temp_left = a[left];
            let temp_right = a[right];
            a.set(left, temp_right);
            a.set(right, temp_left);
            
            left += 1;
            right -= 1;
        }
    }
    
    assert forall|i: int, j: int| 0 <= i < j < a.len() implies !a@[i] || a@[j] by {
        if j <= left {
            assert(!a@[i]);
        } else if i >= left {
            if right < left {
                assert(i > right);
                assert(a@[i]);
            } else {
                assert(i >= left);
                assert(j > left);
                if i <= right {
                    // This case should not happen due to loop termination
                    assert(left >= right);
                    assert(false);
                } else {
                    assert(a@[i]);
                }
            }
        } else {
            assert(i < left);
            assert(!a@[i]);
        }
    }
}
// </vc-code>

fn main() {}
}