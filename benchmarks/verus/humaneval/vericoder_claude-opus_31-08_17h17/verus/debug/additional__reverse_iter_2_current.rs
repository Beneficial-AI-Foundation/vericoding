use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn reverse(a: &[i32]) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == a[a.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == a[n - 1 - j],
        decreases n - i,
    {
        result.push(a[n - 1 - i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}