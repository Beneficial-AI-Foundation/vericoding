// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use ghost variable for nat conversion */
    let ghost mut result_spec: Seq<nat> = Seq::empty();
    let mut result: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            result_spec.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& result[j] == a[j]@.len() as usize
                &&& result_spec[j] == a[j]@.len()
                &&& result_spec[j] >= 0
                &&& (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
            }
    {
        let s = &a[i];
        let len: usize = s.len();
        result.push(len);
        proof {
            result_spec = result_spec.push(a[i]@.len());
        }
        i = i + 1;
    }
    
    let ghost final_result: Vec<nat> = Vec::new();
    proof {
        assert(result.len() == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> result[j] == a[j]@.len() as usize);
    }
    
    let mut final_result: Vec<nat> = Vec::new();
    let mut j: usize = 0;
    while j < result.len()
        invariant
            0 <= j <= result.len(),
            result.len() == a.len(),
            final_result.len() == j,
            forall|k: int| 0 <= k < j ==> {
                &&& final_result[k] == result[k] as nat
                &&& final_result[k] == a[k]@.len()
                &&& final_result[k] >= 0
                &&& (a[k]@.len() == 0 <==> a[k]@ == Seq::<char>::empty())
            }
    {
        let ghost n: nat = result[j] as nat;
        final_result.push(n);
        j = j + 1;
    }
    final_result
}
// </vc-code>

}
fn main() {}