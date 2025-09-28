// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide any() returning an arbitrary value of type T */
spec fn any<T>() -> T
{
    choose|t: T| true
}

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
    /* code modified by LLM (iteration 5): implement resize by cycling elements or using arbitrary values when input is empty */
    let mut result: Vec<T> = Vec::new();
    let mut i: usize = 0;
    while i < new_size
        invariant
            i <= new_size,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                if j < a.len() as int {
                    result[j] == a[j]
                } else if a.len() > 0 {
                    result[j] == a[(j % a.len() as int)]
                } else {
                    true
                }
            },
        decreases new_size - i
    {
        if i < a.len() {
            result.push(a[i]);
        } else if a.len() > 0 {
            let idx = i % a.len();
            result.push(a[idx]);
        } else {
            result.push(any::<T>());
        }
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}