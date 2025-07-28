use vstd::prelude::*;
fn main() {}
verus!{
//IMPL remove_all_greater
pub fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
    requires 
        forall |k1:int,k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2]
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
{  
    /* code modified by LLM (iteration 4): added explicit type annotation to fix compilation error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): restructured loop with proper invariant maintenance */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            /* code modified by LLM (iteration 4): save old result state for reasoning */
            let old_result = result@;
            result.push(v[i]);
            
            /* code modified by LLM (iteration 4): prove that the invariant is maintained after push */
            assert(result@.len() == old_result.len() + 1);
            assert(result@[old_result.len() as int] == v[i]);
            assert(forall |k:int| 0 <= k < old_result.len() ==> result@[k] == old_result[k]);
            
            /* code modified by LLM (iteration 4): prove first part of invariant still holds */
            assert(forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k])) by {
                assert(forall |k:int| 0 <= k < old_result.len() ==> result@[k] == old_result[k]);
                assert(result@[old_result.len() as int] == v[i] && v[i] <= e && v@.contains(v[i]));
            };
            
            /* code modified by LLM (iteration 4): prove second part of invariant still holds */
            assert(forall |k:int| 0 <= k <= i && v[k] <= e ==> result@.contains(v[k])) by {
                assert(forall |k:int| 0 <= k < i && v[k] <= e ==> old_result.contains(v[k]));
                assert(forall |k:int| 0 <= k < old_result.len() ==> result@.contains(old_result[k]));
                assert(result@.contains(v[i]));
            };
        }
        i += 1;
    }
    
    result
}
}