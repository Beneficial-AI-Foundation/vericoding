use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArrayToSeq(a: Vec<i32>) -> (s: Seq<i32>)
    ensures
        s.len() == a@.len(),
        forall|i: int| 0 <= i < a@.len() ==> s[i] == a@[i]
{
    let mut result = Seq::empty();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx as int,
            forall|i: int| 0 <= i < idx as int ==> result[i] == a@[i]
    {
        result = result.push(a[idx]);
        idx += 1;
    }
    
    // Proof that the postcondition holds
    assert(result.len() == a@.len());
    assert(forall|i: int| 0 <= i < a@.len() ==> result[i] == a@[i]);
    
    result
}

}