use vstd::prelude::*;

verus! {

// <vc-helpers>
// helper section left intentionally empty
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
    // impl-start
    let len = a.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant { i <= len; }
        invariant { result.len() == i; }
        invariant { forall|j: int| 0 <= j && j < (i as int) ==>
            result[j as usize] == a[((len as int) - 1 - j) as usize] }
        decreases { (len as int) - (i as int) }
    {
        result.push(a[len - 1 - i]);
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}