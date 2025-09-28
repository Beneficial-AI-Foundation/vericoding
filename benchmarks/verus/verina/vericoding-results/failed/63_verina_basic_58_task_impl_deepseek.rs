// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn double_array_elements_invariant_maintained(i: int, s: &Vec<i32>, result: &Vec<i32>) -> bool
    ensures
        result@.len() == i,
        forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == 2 * s@[j],
{
    true
}
/* helper modified by LLM (iteration 5): fixed spec syntax */
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintain invariant with ghost handling */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == 2 * s@[j],
        decreases (s.len() - i) as nat
    {
        ghost {
            proof {
                assert(double_array_elements_invariant_maintained(i as int, s, &result));
            }
        }
        result.push(2 * s[i]);
        i += 1;
    }
    
    ghost {
        proof {
            assert(double_array_elements_invariant_maintained(i as int, s, &result));
        }
    }
    result
}
// </vc-code>

}
fn main() {}