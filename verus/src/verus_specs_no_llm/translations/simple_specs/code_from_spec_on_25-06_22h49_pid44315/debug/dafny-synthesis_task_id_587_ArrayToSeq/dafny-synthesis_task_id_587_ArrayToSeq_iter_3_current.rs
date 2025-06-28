use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ArrayToSeq(a: Vec<i32>) -> (s: Seq<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s.spec_index(i) == a[i as usize]
{
    let mut result = Seq::empty();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result.spec_index(i) == a[i as usize]
    {
        result = result.push(a[idx]);
        idx += 1;
    }
    
    result
}

}