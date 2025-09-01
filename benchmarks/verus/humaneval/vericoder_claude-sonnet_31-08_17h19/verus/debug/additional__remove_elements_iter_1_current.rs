use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn seq_contains<T: PartialEq>(s: Seq<T>, x: T) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == x
}

proof fn seq_contains_equiv(s: Seq<i32>, x: i32)
    ensures seq_contains(s, x) == in_array(s, x)
{
}

proof fn push_preserves_no_duplicates(v: Vec<i32>, x: i32)
    requires 
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j],
        !seq_contains(v@, x)
    ensures
        forall|i: int, j: int| 0 <= i < j < v@.push(x).len() ==> v@.push(x)[i] != v@.push(x)[j]
{
    let new_v = v@.push(x);
    assert forall|i: int, j: int| 0 <= i < j < new_v.len() implies new_v[i] != new_v[j] by {
        if j == new_v.len() - 1 {
            assert(new_v[j] == x);
            assert(new_v[i] != x);
        }
    }
}

proof fn push_preserves_in_array(v: Vec<i32>, x: i32, orig: Seq<i32>)
    requires forall|k: int| 0 <= k < v.len() ==> in_array(orig, v[k])
    ensures forall|k: int| 0 <= k < v@.push(x).len() ==> (k < v.len() ==> in_array(orig, v@.push(x)[k]))
{
}
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
    
    for i in 0..a.len()
        invariant
            forall|k: int| 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
    {
        let elem = a[i];
        if !in_array(b@, elem) && !seq_contains(c@, elem) {
            proof {
                seq_contains_equiv(c@, elem);
                push_preserves_no_duplicates(c, elem);
                push_preserves_in_array(c, elem, a@);
            }
            c.push(elem);
        }
    }
    
    c
}
// </vc-code>

fn main() {}
}