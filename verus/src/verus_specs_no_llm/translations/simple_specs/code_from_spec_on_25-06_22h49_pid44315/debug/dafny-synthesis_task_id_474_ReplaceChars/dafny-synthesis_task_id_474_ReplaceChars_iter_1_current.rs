use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceChars(s: String, oldChar: char, newChar: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.spec_index(i) == oldChar ==> v.spec_index(i) == newChar) && (s.spec_index(i) != oldChar ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result = String::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> (s.spec_index(j) == oldChar ==> result.spec_index(j) == newChar) && (s.spec_index(j) != oldChar ==> result.spec_index(j) == s.spec_index(j))
    {
        let ch = s.spec_index(i as int);
        if ch == oldChar {
            result.push(newChar);
        } else {
            result.push(ch);
        }
        i += 1;
    }
    
    result
}

}