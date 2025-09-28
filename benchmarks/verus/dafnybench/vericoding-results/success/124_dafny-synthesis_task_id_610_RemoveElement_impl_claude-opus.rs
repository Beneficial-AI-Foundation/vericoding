use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v[i] == s[i],
        forall|i: int| k <= i < v.len() ==> v[i] == s[(i + 1) as int],
// </vc-spec>
// <vc-code>
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            v.len() == if i <= k { i as int } else { (i - 1) as int },
            forall|j: int| 0 <= j < i && j < k ==> v[j] == s[j],
            forall|j: int| k <= j < v.len() ==> v[j] == s[(j + 1) as int],
        decreases s.len() - i,
    {
        if i != k {
            v.push(s[i]);
        }
        i = i + 1;
    }
    
    v
}
// </vc-code>

fn main() {}
}