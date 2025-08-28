use vstd::prelude::*;

verus! {

spec fn strict_negative(v: &Vec<i32>, i: usize, j: usize) -> bool
    recommends 0 <= i <= j <= v.len()
{
    forall|u: usize| i <= u < j ==> v[u as int] < 0
}

spec fn positive(s: Seq<i32>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_permutation(s: Seq<i32>, t: Seq<i32>) -> bool {
    s.to_multiset() == t.to_multiset()
}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
spec fn partitioned_at(v: &Vec<i32>, pivot: usize) -> bool {
    &&& 0 <= pivot <= v.len()
    &&& positive(v@.subrange(0, pivot as int))
    &&& strict_negative(v, pivot, v.len())
}

proof fn lemma_swap_preserves_permutation(v1: Seq<i32>, v2: Seq<i32>, i: int, j: int)
    requires
        0 <= i < v1.len(),
        0 <= j < v1.len(),
        v2.len() == v1.len(),
        v2[i] == v1[j],
        v2[j] == v1[i],
        forall|k: int| 0 <= k < v1.len() && k != i && k != j ==> v2[k] == v1[k]
    ensures
        is_permutation(v1, v2)
{
    assert(v1.to_multiset() =~= v2.to_multiset()) by {
        assert(v1.to_multiset().count(v1[i]) == v2.to_multiset().count(v1[i]));
        assert(v1.to_multiset().count(v1[j]) == v2.to_multiset().count(v1[j]));
        assert(forall|x: i32| v1.to_multiset().count(x) == v2.to_multiset().count(x));
    };
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn separate(v: &mut Vec<i32>) -> (i: usize)
    ensures
        0 <= i <= v.len(),
        positive(v@.subrange(0, i as int)),
        strict_negative(v, i, v.len()),
        is_permutation(v@, old(v)@),
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut left = 0usize;
    let mut right = 0usize;
    
    let ghost original_v = v@;
    
    while right < v.len()
        invariant
            0 <= left <= right <= v.len(),
            positive(v@.subrange(0, left as int)),
            forall|k: usize| left <= k < right ==> v[k as int] < 0,
            is_permutation(v@, original_v),
        decreases v.len() - right
    {
        if v[right] >= 0 {
            if left != right {
                let ghost old_v = v@;
                let temp = v[left];
                let right_val = v[right];
                v.set(left, right_val);
                v.set(right, temp);
                
                proof {
                    assert(left < v@.len());
                    assert(right < v@.len());
                    lemma_swap_preserves_permutation(old_v, v@, left as int, right as int);
                    assert(is_permutation(old_v, v@));
                    assert(is_permutation(original_v, old_v));
                    assert(is_permutation(original_v, v@)) by {
                        assert(original_v.to_multiset() == old_v.to_multiset());
                        assert(old_v.to_multiset() == v@.to_multiset());
                    };
                }
            }
            left += 1;
        }
        right += 1;
    }
    
    left
}
// </vc-code>

fn main() {}

}