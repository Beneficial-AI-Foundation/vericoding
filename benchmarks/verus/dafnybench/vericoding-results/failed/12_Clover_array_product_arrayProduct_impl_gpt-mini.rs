use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers required.
// </vc-helpers>

// <vc-spec>
fn array_product(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] * b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut c: Vec<i32> = Vec::new();
    c.reserve(n as usize);
    let mut i: int = 0;
    while i < n
        invariant i <= n;
        invariant c.len() == (i as usize);
        invariant forall |j: int| 0 <= j && j < i ==>
            a[j as usize] * b[j as usize] == c[j as usize];
        decreases n - i
    {
        let idx: usize = i as usize;
        let ai: i32 = a[idx];
        let bi: i32 = b[idx];
        c.push(ai * bi);
        i += 1;
    }
    // Now i == n and invariants imply the postcondition
    assert(c.len() == n as usize);
    assert(forall |j: int| 0 <= j && j < n ==>
        a[j as usize] * b[j as usize] == c[j as usize]);
    c
}
// </vc-code>

fn main() {}

}