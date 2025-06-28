use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' || c == ',' || c == '.'
}

fn ReplaceWithColon(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == ':') && (!IsSpaceCommaDot(s.spec_index(i)) ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result = String::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (IsSpaceCommaDot(s.spec_index(j)) ==> result.spec_index(j) == ':') && (!IsSpaceCommaDot(s.spec_index(j)) ==> result.spec_index(j) == s.spec_index(j))
    {
        let c = s.as_bytes()[i] as char;
        if IsSpaceCommaDot(c) {
            result.push(':');
        } else {
            result.push(c);
        }
        i += 1;
    }
    
    result
}

}