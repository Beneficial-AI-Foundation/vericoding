use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int {
        invariant(0 <= i && i <= a.len() as int);
        invariant(res.len() == i as usize);
        invariant(forall |j: int| 0 <= j && j < i ==> res[j] == a[j]);
        decreases((a.len() as int) - i);
        res.push(a[i]);
        // after push, the newly pushed element equals a[i]
        assert(res[i] == a[i]);
        i = i + 1;
    }
    res.push(b);
    res
    // impl-end
}
// </vc-code>

fn main() {}
}