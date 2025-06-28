use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> (s.spec_index(i) == ' ' ==> v.spec_index(i) == ch) && (s.spec_index(i) != ' ' ==> v.spec_index(i) == s.spec_index(i))
{
    let mut result = String::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (s.spec_index(j) == ' ' ==> result.spec_index(j) == ch) && (s.spec_index(j) != ' ' ==> result.spec_index(j) == s.spec_index(j))
    {
        let current_char = s.chars().nth(i).unwrap();
        if current_char == ' ' {
            result.push(ch);
        } else {
            result.push(current_char);
        }
        i += 1;
    }
    
    result
}

}