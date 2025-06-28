use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SplitStringIntoChars(s: Seq<char>) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.spec_index(i) == s.spec_index(i)
{
    // Convert seq to vec for iteration
    let s_vec = s.to_vec();
    let mut result: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < s_vec.len()
        invariant
            idx <= s.len(),
            s_vec@ == s,
            result.len() == idx,
            forall |i: int| 0 <= i < idx ==> result@.spec_index(i) == s.spec_index(i)
    {
        result.push(s_vec[idx]);
        idx = idx + 1;
    }
    
    result@
}

}