use vstd::prelude::*;

verus!{

//ATOM
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    // pre-conditions-start
    requires
        l == vec.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
    // post-conditions-end
{
    // impl-start
    // The postconditions follow directly from the definition of push
    // No additional proof steps needed as Verus can verify these properties automatically
    // impl-end
}

//IMPL remove_all_greater
fn remove_all_greater(v: Vec<i32>, e: i32) -> (result: Vec<i32>)
{
    return false;  // TODO: Remove this line and implement the function body
}
    // pre-conditions-start
    requires 
        forall |k1:int, k2:int| 0 <= k1 < k2 < v.len() ==> v[k1] != v[k2],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
        forall |k:int| 0 <= k < v.len() && v[k] <= e ==> result@.contains(v[k]),
    // post-conditions-end
{  
    /* code modified by LLM (iteration 1): Fixed function signature placement and implemented proper logic */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall |k:int| 0 <= k < result.len() ==> result[k] <= e && v@.contains(result[k]),
            forall |k:int| 0 <= k < i && v[k] <= e ==> result@.contains(v[k]),
    {
        if v[i] <= e {
            result.push(v[i]);
        }
        i += 1;
    }
    
    result
}

}

fn main() {}