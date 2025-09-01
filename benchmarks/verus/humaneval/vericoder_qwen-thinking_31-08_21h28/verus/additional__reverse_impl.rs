use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < n {
        result.push(a@[n - 1 - i]);
        i += 1;
    } invariant {
        result.len() == i,
        #[trigger] forall|k: int| 0 <= k && k < result.len() ==>
            result@[k] == a@[n - 1 - k]
    }
    result
}
// </vc-code>

fn main() {}
}