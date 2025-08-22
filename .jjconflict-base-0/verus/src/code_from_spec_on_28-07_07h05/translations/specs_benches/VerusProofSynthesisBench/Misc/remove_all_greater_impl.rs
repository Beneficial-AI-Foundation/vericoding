use vstd::prelude::*;

verus!{
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
{  
    /* code modified by LLM (iteration 4): added explicit type annotation Vec<i32> to fix compilation error */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): restructured the loop body to ensure invariant is maintained */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            result.push(v[i]);
            /* code modified by LLM (iteration 4): fixed type mismatch by casting i to int */
            assert(result@.contains(v[i as int]));
        }
        i += 1;
        /* code modified by LLM (iteration 4): fixed type mismatch in assertion by casting i to int */
        assert(forall |k:int| 0 <= k < i as int && v[k] <= e ==> result@.contains(v[k]));
    }
    
    result
}
}

fn main() {}