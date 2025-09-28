// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn zeros_like(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0,
        forall|v: &Vec<i32>| v.len() == result.len() ==> {
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] + v[i] == v[i] && v[i] + result[i] == v[i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type mismatches by removing 'as usize' casts from vector indexing */
    let mut result: Vec<i32> = Vec::new();
    let len = a.len();
    proof {
        assert(result.len() == 0);
    }
    for i in 0..len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == 0,
    {
        result.push(0);
    }
    proof {
        assert(result.len() == len);
        assert(forall|i: int| 0 <= i < len ==> result[i] == 0);
        assert(forall|v: Seq<i32>| v.len() == len ==> {
            forall|i: int| 0 <= i < len ==> result[i] + v[i] == v[i]
        });
    }
    result
}
// </vc-code>

}
fn main() {}