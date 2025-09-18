// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type conversion issues and added proper lemma for vector indexing */
proof fn lemma_vec_forall_nonzero(a: Seq<f32>, i: int)
    requires 0 <= i <= a.len()
    ensures (forall|j: int| i <= j < a.len() ==> a[j] != 0.0f32) ==> (forall|j: int| 0 <= j < a.len() ==> a[j] != 0.0f32)
{
    if i > 0 {
        lemma_vec_forall_nonzero(a, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn all(a: Vec<f32>) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32),
        (a.len() == 0 ==> result == true),
        ((exists|i: int| 0 <= i < a.len() && a[i] == 0.0f32) ==> result == false),
        ((forall|i: int| 0 <= i < a.len() ==> a[i] != 0.0f32) ==> result == true),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors by using usize for indexing and proper sequence conversion */
{
    let mut i: usize = 0;
    let mut result = true;
    let s = a@;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result == (forall|j: int| 0 <= j < i ==> s[j] != 0.0f32),
            (forall|k: int| i <= k < a.len() ==> s[k] != 0.0f32) ==> result == (forall|j: int| 0 <= j < a.len() ==> s[j] != 0.0f32)
        decreases a.len() - i
    {
        if s[i as int] == 0.0f32 {
            result = false;
            break;
        } else {
            i = i + 1;
        }
    }
    
    if result {
        lemma_vec_forall_nonzero(s, i as int);
    }
    
    result
}
// </vc-code>

}
fn main() {}