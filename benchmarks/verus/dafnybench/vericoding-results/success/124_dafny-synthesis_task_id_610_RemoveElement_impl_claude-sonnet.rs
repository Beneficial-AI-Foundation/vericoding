use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            k < s.len(),
            result.len() == if i <= k { i } else { (i - 1) as usize },
            forall|j: int| 0 <= j < i && j < k ==> result[j] == s[j],
            forall|j: int| k < j < i ==> result[(j - 1) as int] == s[j],
        decreases s.len() - i,
    {
        if i != k {
            result.push(s[i]);
        }
        i += 1;
    }
    
    proof {
        assert(result.len() == s.len() - 1);
        assert(forall|j: int| 0 <= j < k ==> result[j] == s[j]);
        assert(forall|j: int| k <= j < result.len() ==> result[j] == s[(j + 1) as int]);
    }
    
    result
}
// </vc-code>

fn main() {}
}