use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn is_in(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

#[verifier::loop_isolation(false)]
fn contains(v: &Vec<i32>, x: i32) -> (found: bool) 
    ensures found == is_in(v@, x)
{
    let mut idx = 0;
    while idx < v.len() 
        invariant 
            idx <= v.len(),
            forall|j: nat| j < idx ==> #[trigger] v@[j] != x
    {
        if v[idx] == x {
            proof {
                assert( exists|j: int| 0 <= j < v.len() && v@[j] == x );
            }
            return true;
        }
        idx += 1;
    }
    proof {
        assert(!is_in(v@, x));
    }
    false
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
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
{
    let mut c: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len() 
        invariant 
            i <= a.len(),
            forall|k: int| 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|p: int, q: int| 0 <= p < q < c.len() ==> c[p] != c[q]
        decreases a.len() - i
    {
        let value = a[i];
        let in_b = contains(b, value);
        let in_c = contains(&c, value);
        if !in_b && !in_c {
            c.push(value);
        }
        i += 1;
    }
    c
}
// </vc-code>

fn main() {}
}