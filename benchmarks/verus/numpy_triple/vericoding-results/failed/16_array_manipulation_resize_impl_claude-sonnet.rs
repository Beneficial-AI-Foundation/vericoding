// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed helper function as it's not needed for the implementation */
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
    /* code modified by LLM (iteration 5): Fixed type error by avoiding int cast in exec code */
    if new_size == 0 {
        return Vec::new();
    }
    
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < new_size
        invariant
            result.len() == i,
            i <= new_size,
            a.len() > 0,
            forall|j: int| 0 <= j < i ==> {
                if j < a.len() {
                    result[j] == a[j]
                } else {
                    result[j] == a[(j % a.len() as int) as int]
                }
            }
    {
        if i < a.len() {
            result.push(a[i]);
        } else {
            let idx = i % a.len();
            result.push(a[idx]);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}