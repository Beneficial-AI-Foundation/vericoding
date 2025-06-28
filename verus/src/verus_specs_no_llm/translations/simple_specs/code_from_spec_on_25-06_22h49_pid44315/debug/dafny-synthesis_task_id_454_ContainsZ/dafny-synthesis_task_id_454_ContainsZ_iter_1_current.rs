use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsZ(s: String) -> (result: bool)
    ensures
        result <==> (exists|i: int| 0 <= i < s.len() && (s.spec_index(i) == 'z' || s.spec_index(i) == 'Z'))
{
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !(s.spec_index(j) == 'z' || s.spec_index(j) == 'Z')
    {
        let c = s.as_bytes()[i];
        if c == b'z' || c == b'Z' {
            return true;
        }
        i += 1;
    }
    false
}

}