use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>

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
    let mut c: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() {
        invariant forall|j: int| 0 <= j && j < c.len() ==> in_array(a@, c[j]) && !in_array(b@, c[j]);
        invariant forall|j: int, k: int| 0 <= j && j < k && k < c.len() ==> c[j] != c[k];
        if !in_array(b@, a[i]) && !in_array(c@, a[i]) {
            c.push(a[i]);
        }
        i = i + 1;
    }
    c
}
// </vc-code>

fn main() {}
}