// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed invariant syntax and spec indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> 
                if k == (j as int) {
                    result[k] == 60
                } else {
                    result[k] == a[k]
                },
        decreases(a.len() - i)
    {
        if i == j {
            result.push(60);
        } else {
            result.push(a[i]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}