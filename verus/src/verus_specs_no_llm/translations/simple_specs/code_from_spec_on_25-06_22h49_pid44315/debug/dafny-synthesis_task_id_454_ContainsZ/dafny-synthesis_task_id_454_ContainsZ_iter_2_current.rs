use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsZ(s: &str) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z')
    {
        let c = s.spec_index(i as int);
        if c == 'z' || c == 'Z' {
            assert(exists|k: int| 0 <= k < s.len() && (s.spec_index(k) == 'z' || s.spec_index(k) == 'Z'));
            return true;
        }
        assert(!(s.spec_index(i as int) == 'z' || s.spec_index(i as int) == 'Z'));
        i += 1;
    }
    
    assert(forall|j: int| 0 <= j < s.len() ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z'));
    assert(!(exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z')));
    
    false
}

}