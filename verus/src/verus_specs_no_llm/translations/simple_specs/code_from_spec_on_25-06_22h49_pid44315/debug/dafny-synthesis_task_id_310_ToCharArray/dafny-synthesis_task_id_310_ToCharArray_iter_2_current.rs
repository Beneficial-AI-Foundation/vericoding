use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ToCharArray(s: Seq<char>) -> (a: Vec<char>)
    ensures
        a.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> a.spec_index(i) == s.spec_index(i)
{
    let mut a = Vec::new();
    let mut idx = 0;
    
    while idx < s.len()
        invariant
            a.len() == idx,
            forall|i: int| 0 <= i < idx ==> a.spec_index(i) == s.spec_index(i)
    {
        a.push(s.spec_index(idx));
        idx = idx + 1;
    }
    
    a
}

}