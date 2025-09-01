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
    let mut c = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            forall|k: int| 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|j1: int, j2: int| 0 <= j1 < j2 < c.len() ==> c[j1] != c[j2],
        decreases(a.len() - i),
    {
        let x = a[i];
        if !b.contains(&x) && !c.contains(&x) {
            c.push(x);
            proof {
                assert(in_array(a@, x));
                assert(!in_array(b@, x));
                assert(forall|j: int| 0 <= j < c.len() - 1 ==> c[j] != x);
            }
        }
        i += 1;
    }
    c
}
// </vc-code>

fn main() {}
}