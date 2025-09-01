use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// <vc-helpers>
proof fn index_in_array(a: &Vec<i32>, i: int)
    requires 0 <= i && i < a.len()
    ensures in_array(a@, a.index(i))
{
    proof {
        // a.index(i) corresponds to the sequence view a@[i]
        assert(a.index(i) == a@[i]);
        assert(exists|j: int| 0 <= j < a.len() && a@[j] == a.index(i));
    }
}
// </vc-helpers>
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
// <vc-code>
{
    // impl-start
    let mut c: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() {
        invariant 0 <= i && i <= a.len();
        invariant c.len() <= a.len();
        invariant forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]);
        invariant forall|p: int, q: int| 0 <= p < q < c.len() ==> c[p] != c[q];
        decreases a.len() - i;
        let x: i32 = a.index(i);
        if !in_array(b@, x) && !in_array(c@, x) {
            // show that x is in a (so pushing preserves the a-membership invariant)
            index_in_array(a, i);
            c.push(x);
        }
        i += 1;
    }
    c
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}