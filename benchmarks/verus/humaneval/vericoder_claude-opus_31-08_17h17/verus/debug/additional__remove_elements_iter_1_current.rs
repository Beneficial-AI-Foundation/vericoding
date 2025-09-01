use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// Helper to check if an element has already been added to the result
spec fn already_in_result(result: Seq<i32>, x: i32, len: int) -> bool {
    exists|k: int| 0 <= k < len && result[k] == x
}

// Helper lemma to prove uniqueness is preserved
proof fn uniqueness_preserved(result: Seq<i32>, len: int)
    requires
        forall|i: int, j: int| 0 <= i < j < len ==> result[i] != result[j],
        len < result.len(),
    ensures
        forall|i: int, j: int| 0 <= i < j < len ==> result[i] != result[j],
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
            forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
            forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
            c.len() <= i,
    {
        let elem = a[i];
        
        // Check if elem is in b
        let mut in_b = false;
        for j in 0..b.len()
            invariant
                in_b == exists|k: int| 0 <= k < j && b[k] == elem,
        {
            if b[j] == elem {
                in_b = true;
            }
        }
        
        if !in_b {
            // Check if elem is already in c
            let mut already_added = false;
            for k in 0..c.len()
                invariant
                    already_added == exists|m: int| 0 <= m < k && c[m] == elem,
                    forall|m: int| #![auto] 0 <= m < c.len() ==> in_array(a@, c[m]) && !in_array(b@, c[m]),
                    forall|p: int, q: int| 0 <= p < q < c.len() ==> c[p] != c[q],
            {
                if c[k] == elem {
                    already_added = true;
                }
            }
            
            if !already_added {
                assert(in_array(a@, elem)) by {
                    assert(a@[i as int] == elem);
                }
                assert(!in_array(b@, elem)) by {
                    assert(forall|k: int| 0 <= k < b.len() ==> b[k] != elem);
                }
                c.push(elem);
            }
        }
    }
    
    c
}
// </vc-code>

fn main() {}
}