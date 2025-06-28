use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitStringIntoChars(s: String) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.spec_index(i) == s.spec_index(i)
{
    let mut result: Vec<char> = Vec::new();
    let mut idx = 0;
    
    while idx < s.len()
        invariant
            idx <= s.len(),
            result.len() == idx,
            forall |i: int| 0 <= i < idx ==> result.spec_index(i) == s.spec_index(i)
    {
        result.push(s.spec_index(idx));
        idx = idx + 1;
    }
    
    result.as_seq()
}

}