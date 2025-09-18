// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix vec_push_spec implementation to satisfy postconditions */
proof fn vec_push_spec<T>(v: &mut Vec<T>, val: T)
    ensures
        v.len() == old(v).len() + 1,
        forall|j: int| 0 <= j < old(v).len() ==> v@[j] == old(v)@[j],
        v@[old(v).len() as int] == val
{
    let old_len = v.len() as int;
    v.push(val);
    assert(v@.len() == old_len + 1) by {
        vstd::vec::push_spec(v, val);
    }
    assert(forall|j: int| 0 <= j < old_len ==> v@[j] == old(v)@[j]) by {
        vstd::vec::push_spec(v, val);
    }
    assert(v@[old_len] == val) by {
        vstd::vec::push_spec(v, val);
    }
}

spec fn result_index_spec(result: Vec<Vec<f32>>, arr1: Seq<f32>, arr2: Seq<f32>, j: int) -> bool
    recommends 0 <= j < result.len()
{
    #[trigger] result@[j].len() == 2 && #[trigger] result@[j]@[0] == arr1[j] && #[trigger] result@[j]@[1] == arr2[j]
}
// </vc-helpers>

// <vc-spec>
fn c_(arr1: Vec<f32>, arr2: Vec<f32>) -> (result: Vec<Vec<f32>>)
    requires arr1.len() == arr2.len(),
    ensures 
        result.len() == arr1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i].len() == 2 &&
            result[i][0] == arr1[i] &&
            result[i][1] == arr2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix loop invariant and ensure proper vector bounds checking */
{
    let mut result = Vec::new();
    let n = arr1.len() as usize;
    
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result_index_spec(result, arr1@, arr2@, j)
        decreases n - i
    {
        let mut pair = Vec::new();
        proof {
            vec_push_spec(&mut pair, arr1[i]);
            vec_push_spec(&mut pair, arr2[i]);
        }
        pair.push(arr1[i]);
        pair.push(arr2[i]);
        proof {
            vec_push_spec(&mut result, pair);
        }
        result.push(pair);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}