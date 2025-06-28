use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn max(s: Vec<nat>) -> (a: int)
    requires
        s.len() > 0
    ensures
        forall|x: int| 0 <= x < s.len() ==> a >= s.spec_index(x),
        exists|i: int| 0 <= i < s.len() && a == s.spec_index(i)
{
    let mut max_val: int = s[0] as int;
    let mut i: usize = 1;
    
    while i < s.len()
        invariant
            0 < i <= s.len(),
            forall|j: int| 0 <= j < i ==> max_val >= s.spec_index(j),
            exists|k: int| 0 <= k < i && max_val == s.spec_index(k)
    {
        if s[i] as int > max_val {
            max_val = s[i] as int;
        }
        i += 1;
    }
    
    max_val
}

}