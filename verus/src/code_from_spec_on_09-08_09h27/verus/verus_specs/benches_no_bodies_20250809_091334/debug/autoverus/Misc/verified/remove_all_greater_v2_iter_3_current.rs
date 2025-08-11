use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
    let pushed = vec.push(i);
    
    // The proof is straightforward from the definition of push
    // push appends the element to the end, so all original indices are preserved
    assert(pushed.len() == vec.len() + 1);
    assert(pushed.index(l as int) == i);
    
    // For all original indices, the elements remain the same
    assert forall |k: int| 0 <= k < vec.len() implies vec[k] == pushed[k] by {
        // This follows from the definition of Seq::push
    }
}

pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    /* code modified by LLM (iteration 1): Added explicit type annotation to fix compilation error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }
    
    result
}
}