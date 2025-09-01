use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// No additional helpers required for this implementation.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    // post-conditions-start
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut c: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() {
        invariant 0 <= i <= a.len();
        invariant c.len() <= a.len();
        invariant forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]);
        invariant forall|p: int, q: int| 0 <= p < q < c.len() ==> c[p] != c[q];
        let x: i32 = a.index(i);
        if !in_array(b@, x) && !in_array(c@, x) {
            // show that pushing x preserves the invariants
            // after push, new element x satisfies membership and not-in-b,
            // and is distinct from all existing elements because !in_array(c@, x).
            c.push(x);
        }
        i += 1;
    }
    c
    // impl-end
}
// </vc-code>

fn main() {}
}