use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(s: Vec<nat>) -> (a: nat)
    requires 
        s.len() > 0
    ensures 
        forall|x: int| 0 <= x < s.len() ==> a >= s[x],
        exists|i: int| 0 <= i < s.len() && a == s[i]
{
    let mut max_val = s[0];
    let mut i = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            s.len() > 0,
            exists|j: int| 0 <= j < i && max_val == s[j],
            forall|k: int| 0 <= k < i ==> max_val >= s[k]
    {
        if s[i] > max_val {
            max_val = s[i];
        }
        i = i + 1;
    }
    
    max_val
}

// Test function to verify the implementation
fn test_max() {
    let v = Vec::<nat>::new();
    // Note: Cannot easily test with literal vectors in Verus specs
    // This is a placeholder test function
}

}