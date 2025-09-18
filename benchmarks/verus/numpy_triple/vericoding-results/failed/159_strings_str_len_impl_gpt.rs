// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple pure min function as a placeholder helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
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
    /* code modified by LLM (iteration 5): build result by iterating and using exec string length; assert relation to spec length to satisfy invariants */
    let mut result: Vec<nat> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result[j] == a[j]@.len()
        decreases a.len() - i
    {
        let len_i_exec: usize = a[i].len();
        let len_i: nat = len_i_exec as nat;
        proof {
            assert(a[i]@.len() == a[i].len() as nat);
        }
        result.push(len_i);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}