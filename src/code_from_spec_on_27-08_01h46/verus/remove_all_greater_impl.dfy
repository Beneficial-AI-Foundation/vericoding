use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn contains_at_most_once<T>(s: Seq<T>) -> bool {
    forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

proof fn lemma_filter_preserves_uniqueness(v: Vec<i32>, e: i32)
    requires
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    ensures
        forall |k1:int,k2:int| 0 <= k1 < k2 < v@.filter(|x: i32| x <= e).len() ==> 
            #[trigger] v@.filter(|x: i32| x <= e)[k1] != #[trigger] v@.filter(|x: i32| x <= e)[k2],
{
}

proof fn lemma_filtered_elements_in_original(v: Vec<i32>, e: i32)
    ensures
        forall |k:int| 0 <= k < v@.filter(|x: i32| x <= e).len() ==> 
            v@.contains(v@.filter(|x: i32| x <= e)[k]),
{
}

proof fn lemma_original_filtered_elements_in_result(v: Vec<i32>, e: i32)
    ensures
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> 
            v@.filter(|x: i32| x <= e).contains(v[k]),
{
}
// </vc-helpers>

// <vc-spec>
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    // pre-conditions-start
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i,
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i = i + 1;
    }
    
    proof {
        lemma_filtered_elements_in_original(v, e);
        lemma_original_filtered_elements_in_result(v, e);
    }
    
    result
}
// </vc-code>

}

fn main() {}