use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Match(s: String, p: String) -> (b: bool)
    requires
        s.len() == p.len()
    ensures
        b <==> forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char
{
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |n: int| 0 <= n < i ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char
    {
        let s_char = s.spec_index(i as int);
        let p_char = p.spec_index(i as int);
        
        if s_char != p_char && p_char != ('?' as char) {
            assert(s_char != p_char && p_char != ('?' as char));
            assert(!(s.spec_index(i as int) == p.spec_index(i as int) || p.spec_index(i as int) == '?' as char));
            assert(exists |n: int| 0 <= n < s.len() && !(s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char));
            return false;
        }
        i += 1;
    }
    
    assert(i == s.len());
    assert(forall |n: int| 0 <= n < s.len() ==> s.spec_index(n) == p.spec_index(n) || p.spec_index(n) == '?' as char);
    return true;
}

}