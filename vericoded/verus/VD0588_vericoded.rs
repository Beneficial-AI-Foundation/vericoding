use vstd::prelude::*;

verus! {

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
    let mut b = Vec::new();
    let mut j = 0;
    
    while j < a.len()
        invariant
            j <= a.len(),
            b.len() == j,
            forall|k: int| 0 <= k < j ==> #[trigger] b@[k] == a@[a.len() - k - 1],
        decreases a.len() - j
    {
        let idx = a.len() - 1 - j;
        b.push(a[idx]);
        j = j + 1;
    }
    
    assert(b.len() == a.len());
    assert(forall|i: int| 0 <= i < a.len() ==> #[trigger] b@[i] == a@[a.len() - i - 1]);
    
    b
}
// </vc-code>

fn main() {
}

}