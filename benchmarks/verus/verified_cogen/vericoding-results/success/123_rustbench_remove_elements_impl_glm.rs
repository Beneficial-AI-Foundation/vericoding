// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_elements(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    ensures
        forall|k: int| #![auto] 0 <= k < c.len() ==> in_array(a@, c[k]) && !in_array(b@, c[k]),
        forall|i: int, j: int| 0 <= i < j < c.len() ==> c[i] != c[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): split loop invariants and added inner loop invariants to fix verification */
{
    let mut c: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < c.len() ==> in_array(a@, c[k]),
            forall|k: int| 0 <= k < c.len() ==> !in_array(b@, c[k]),
            forall|j: int, k: int| 0 <= j < k < c.len() ==> c[j] != c[k],
        decreases a.len() - i,
    {
        let x = a[i];
        i = i + 1;
        
        let mut in_b = false;
        let mut j = 0;
        while j < b.len()
            invariant 
                0 <= j <= b.len(),
                in_b ==> exists|j0: int| 0 <= j0 < j && b[j0] == x,
                !in_b ==> forall|j0: int| 0 <= j0 < j ==> b[j0] != x,
            decreases b.len() - j,
        {
            if b[j] == x {
                in_b = true;
                break;
            }
            j = j + 1;
        }
        
        if in_b {
            continue;
        }
        
        let mut in_c = false;
        let mut k = 0;
        while k < c.len()
            invariant 
                0 <= k <= c.len(),
                in_c ==> exists|k0: int| 0 <= k0 < k && c[k0] == x,
                !in_c ==> forall|k0: int| 0 <= k0 < k ==> c[k0] != x,
            decreases c.len() - k,
        {
            if c[k] == x {
                in_c = true;
                break;
            }
            k = k + 1;
        }
        
        if !in_c {
            c.push(x);
        }
    }
    c
}
// </vc-code>

}
fn main() {}