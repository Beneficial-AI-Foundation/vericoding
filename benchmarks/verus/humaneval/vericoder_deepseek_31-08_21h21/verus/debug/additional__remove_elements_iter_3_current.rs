use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn seq_contains(seq: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == x
}

spec fn no_duplicates(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
}

proof fn remove_elements_helper(a: Seq<i32>, b: Seq<i32>, c: Seq<i32>, k: int)
    requires
        0 <= k < c.len(),
        seq_contains(a, c[k]),
        !seq_contains(b, c[k]),
    ensures
        seq_contains(a, c[k]) && !seq_contains(b, c[k]),
{
}

spec fn in_array_spec(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
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
    let mut c: Vec<i32> = Vec::new();
    let mut seen: Vec<i32> = Vec::new();
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            forall|k: int| 0 <= k < c.len() ==> seq_contains(a@, c@[k]) && !seq_contains(b@, c@[k]),
            forall|idx: int| 0 <= idx < seen.len() ==> seq_contains(a@, seen@[idx]),
            forall|idx: int| 0 <= idx < c.len() ==> seq_contains(seen@, c@[idx]),
            no_duplicates(c@),
    {
        let elem = a[i];
        if !seq_contains(b@, elem) {
            if !seq_contains(seen@, elem) {
                c.push(elem);
                seen.push(elem);
            }
        }
        i += 1;
    }
    c
}
// </vc-code>

fn main() {}
}