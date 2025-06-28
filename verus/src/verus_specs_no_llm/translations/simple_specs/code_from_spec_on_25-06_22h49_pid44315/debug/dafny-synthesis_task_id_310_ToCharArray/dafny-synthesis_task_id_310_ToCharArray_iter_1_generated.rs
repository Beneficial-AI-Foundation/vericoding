use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ToCharArray(s: String) -> (a: Vec<char>)
    ensures
        a.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i)
{
    let a = s.chars().collect::<Vec<char>>();
    
    proof {
        // The postconditions should be satisfied by the semantics of chars().collect()
        // In Verus, the conversion from String to Vec<char> via chars().collect()
        // preserves the character sequence and length
        assert(a.len() == s.len());
        assert(forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i));
    }
    
    a
}

}