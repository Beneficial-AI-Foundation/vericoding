use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut c: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant i <= n;
        invariant c.len() == i;
        invariant forall |j: int| 0 <= j && j < i as int ==> a[j as nat] + b[j as nat] == c[j as nat];
    {
        c.push(a[i] + b[i]);
        i = i + 1;
    }
    c
}
// </vc-code>

fn main() {}

}