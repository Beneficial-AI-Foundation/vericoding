use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Match(s: String, p: String) -> (b: bool)
    requires
        s.len() == p.len()
    ensures
        b <==> forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?'
{
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |n: int| 0 <= n < i ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?'
    {
        if s[i] != p[i] && p[i] != '?' {
            return false;
        }
        i += 1;
    }
    
    return true;
}

}