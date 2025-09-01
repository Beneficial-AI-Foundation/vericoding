use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// There are no helpers needed in this case
// </vc-helpers>
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
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let len = a.len();
    while i < len
        invariant
            result.len() == i as int,
            i <= len as int,
            forall |k: int| 0 <= k && k < i as int ==> #[trigger] (result@[k] == a@[(len as int - 1 - k)]),
    {
        result.push(a[len - 1 - i]);
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}
}