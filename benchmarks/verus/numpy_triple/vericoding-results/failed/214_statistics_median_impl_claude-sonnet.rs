// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed sort_preserves_multiset proof and sort_vec multiset preservation */
use vstd::multiset::Multiset;

spec fn multiset_of_seq<T>(s: Seq<T>) -> Multiset<T> {
    s.to_multiset()
}

proof fn sort_preserves_multiset(original: Seq<int>, sorted: Seq<int>)
    requires
        multiset_of_seq(original) == multiset_of_seq(sorted),
        is_sorted(sorted),
    ensures
        sorted.len() == original.len(),
{
    assert(sorted.len() == original.len()) by {
        assert(sorted.to_multiset() == original.to_multiset());
    }
}

fn sort_vec(v: &mut Vec<i8>)
    ensures
        multiset_of_seq(old(v)@) == multiset_of_seq(v@),
        is_sorted(v@.map(|i: int, x: i8| x as int)),
        v@.len() == old(v)@.len(),
{
    let n = v.len();
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == n,
            multiset_of_seq(old(v)@) == multiset_of_seq(v@),
            forall|k: int, l: int| 0 <= k < l < i ==> v@[k] <= v@[l],
        decreases n - i
    {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j]
            invariant
                j <= i,
                i < n,
                v@.len() == n,
                multiset_of_seq(old(v)@) == multiset_of_seq(v@),
            decreases j
        {
            let temp = v[j];
            v.set(j, v[j - 1]);
            v.set(j - 1, temp);
            j -= 1;
        }
        i += 1;
    }
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

fn median(a: Vec<i8>) -> (result: i8)
    requires a.len() > 0,
    ensures 
        exists|sorted: Seq<int>| #[trigger] sorted.len() == a@.len() &&
            is_sorted(sorted) &&
            (if a.len() % 2 == 1 {
                result as int == sorted[((a.len() - 1) / 2) as int]
            } else {
                result as int == (sorted[(a.len() / 2 - 1) as int] + sorted[(a.len() / 2) as int]) / 2
            })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified proof to rely on sort_vec postconditions */
    let mut vec_copy = a.clone();
    sort_vec(&mut vec_copy);
    
    let len = vec_copy.len();
    
    proof {
        let sorted_seq = vec_copy@.map(|i: int, x: i8| x as int);
        assert(sorted_seq.len() == a@.len()) by {
            assert(vec_copy@.len() == a@.len());
        }
        assert(is_sorted(sorted_seq));
    }
    
    if len % 2 == 1 {
        let mid_idx = (len - 1) / 2;
        vec_copy[mid_idx]
    } else {
        let left_idx = len / 2 - 1;
        let right_idx = len / 2;
        let left_val = vec_copy[left_idx] as i32;
        let right_val = vec_copy[right_idx] as i32;
        ((left_val + right_val) / 2) as i8
    }
}
// </vc-code>


}
fn main() {}