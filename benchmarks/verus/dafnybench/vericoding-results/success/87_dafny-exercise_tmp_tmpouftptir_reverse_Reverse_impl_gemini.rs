// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn reverse(a: &Vec<char>) -> (b: Vec<char>)
    requires 
        a.len() > 0,
    ensures 
        b.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> b[i] == a[a.len() - i - 1],
// </vc-spec>
// <vc-code>
{
    let mut b: Vec<char> = Vec::new();
    let mut j: usize = 0;

    while j < a.len()
        invariant
            0 <= j <= a.len(),
            b.len() == j,
            forall|k: int| 0 <= k < j ==> b[k] == a[a.len() - 1 - k],
        decreases a.len() - j
    {
        let val = a[a.len() - 1 - j];
        b.push(val);
        j = j + 1;
    }

    b
}
// </vc-code>

}
fn main() {}