// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sorted(v: &Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]
}

/* helper modified by LLM (iteration 5): fixed postconditions and invariants for insert_sorted */
fn insert_sorted(sorted_vec: &mut Vec<i32>, elem: i32)
    requires
        old(sorted_vec).len() < usize::MAX,
        sorted(old(sorted_vec)),
    ensures
        sorted(sorted_vec),
        sorted_vec@.to_multiset() == old(sorted_vec)@.to_multiset().insert(elem),
        sorted_vec@.len() == old(sorted_vec)@.len() + 1,
{
    let mut i: usize = 0;
    while i < sorted_vec.len()
        invariant
            i <= sorted_vec.len(),
            sorted_vec@.len() == old(sorted_vec)@.len(),
            forall|j: int| 0 <= j < i ==> sorted_vec[j] <= elem,
            forall|j: int| i <= j < sorted_vec.len() ==> sorted_vec[j] == old(sorted_vec)[j],
            forall|j: int, k: int| 0 <= j < k < i ==> sorted_vec[j] <= sorted_vec[k],
            forall|j: int, k: int| i <= j < k < sorted_vec.len() ==> sorted_vec[j] <= sorted_vec[k],
            sorted_vec@.to_multiset() == old(sorted_vec)@.to_multiset(),
        decreases sorted_vec.len() - i
    {
        if sorted_vec[i] > elem {
            break;
        }
        i = i + 1;
    }
    sorted_vec.insert(i, elem);
    proof {
        assert(sorted_vec@.len() == old(sorted_vec)@.len() + 1);
        assert(sorted_vec[i as int] == elem);
        assert forall|j: int| 0 <= j < i ==> sorted_vec[j] <= elem by {
            assert(sorted_vec[j] == old(sorted_vec)[j]);
        }
        assert forall|j: int| i < j < sorted_vec.len() ==> elem <= sorted_vec[j] by {
            assert(sorted_vec[j] == old(sorted_vec)[j - 1]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed multiset! macro usage */
    let mut result = Vec::new();
    let mut idx: usize = 0;
    
    proof {
        assert(result@.to_multiset() == Multiset::<i32>::empty());
        assert(l@.subrange(0, 0).to_multiset() == Multiset::<i32>::empty());
    }
    
    while idx < l.len()
        invariant
            idx <= l.len(),
            sorted(&result),
            result@.len() == idx,
            result@.len() <= usize::MAX,
            forall|i: int| 0 <= i < idx ==> exists|j: int| 0 <= j < result.len() && result[j] == l[i],
            result@.to_multiset() == l@.subrange(0, idx as int).to_multiset(),
        decreases l.len() - idx
    {
        let elem = l[idx];
        insert_sorted(&mut result, elem);
        idx = idx + 1;
        
        proof {
            assert(result@.to_multiset() == old(result)@.to_multiset().insert(elem));
            assert(l@.subrange(0, idx as int).to_multiset() == l@.subrange(0, (idx - 1) as int).to_multiset().insert(l[(idx - 1) as int]));
        }
    }
    
    proof {
        assert(idx == l.len());
        assert(l@.subrange(0, l.len() as int) =~= l@);
        assert(result@.to_multiset() == l@.to_multiset());
    }
    
    result
}
// </vc-code>

}
fn main() {}