use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_copy(a: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < n {
        invariant
            i <= n &&
            result.len() == i &&
            forall j: int, 0 <= j < i ==> #[trigger] result[j] == a[j]
        ;
        result.push(a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}