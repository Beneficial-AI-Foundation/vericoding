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
    /* code modified by LLM (iteration 1): Added explicit type annotation Vec<i32> to fix compilation error E0282 */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): Fixed loop invariant to properly maintain the condition */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
        decreases v.len() - i
    {
        if v[i] <= e {
            /* code modified by LLM (iteration 4): Fixed type mismatch by using i as int for contains method */
            assert(v@.contains(v[i as int]));
            result.push(v[i]);
            /* code modified by LLM (iteration 3): Added assertion to help prove the invariant is maintained */
            assert(forall |k:int| 0 <= k < i+1 && v[k] <= e ==> result@.contains(v[k]));
        } else {
            /* code modified by LLM (iteration 3): Added assertion to help prove invariant when element is not added */
            assert(forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]));
            assert(forall |k:int| 0 <= k < i+1 && v[k] <= e ==> result@.contains(v[k]));
        }
        i += 1;
    }
    
    result
}
}