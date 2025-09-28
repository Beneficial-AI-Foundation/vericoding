// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Remove clone() calls since T is not bounded by Clone trait */
    let mut result = Vec::new();
    
    if a.len() == 0 {
        return result;
    }
    
    let ghost_a = a@;
    let mut i: usize = 0;
    while i < new_size
        invariant
            i <= new_size,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < a.len() {
                    result@[j] == ghost_a[j]
                } else {
                    result@[j] == ghost_a[(j % a.len() as int) as int]
                }
            }
    {
        if i < a.len() {
            result.push(a[i as int]);
        } else {
            let idx = (i % a.len()) as int;
            result.push(a[idx]);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}