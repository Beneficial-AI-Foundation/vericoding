use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (c: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        c.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] + b[i] == c[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut c = Vec::new();
    let mut i = 0usize;
    
    while i < a.len()
        invariant
            c.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] + b@[j] == c@[j],
        decreases a.len() - i,
    {
        let sum = a[i] + b[i];
        c.push(sum);
        i += 1;
    }
    
    c
}
// </vc-code>

fn main() {}

}