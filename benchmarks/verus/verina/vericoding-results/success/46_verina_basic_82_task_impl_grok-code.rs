// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_front(a: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures
        a.len() > 0,
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i + 1],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed compilation error by removing unnecessary proof block with empty assert forall that caused syntax error */
{
    let mut result: Vec<i32> = Vec::new();
    proof {
        assert(result@.len() == 0);
    }
    for i in 1..(a.len())
        invariant
            result@.len() == (i as int - 1),
            forall|j: int| 0 <= j < result@.len() ==> result@[j] == a@[(j + 1)]
        decreases a.len() - i
    {
        result.push(a[i]);
        proof {
            assert(result@[(result@.len() - 1)] == a@[i as int]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}