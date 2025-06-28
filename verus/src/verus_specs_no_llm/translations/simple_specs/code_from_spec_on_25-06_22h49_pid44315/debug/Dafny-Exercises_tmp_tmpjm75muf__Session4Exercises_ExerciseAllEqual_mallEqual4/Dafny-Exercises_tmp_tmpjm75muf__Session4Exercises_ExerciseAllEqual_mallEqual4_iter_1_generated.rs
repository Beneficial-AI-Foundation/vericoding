// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall i,j::0<=i<s.len() && 0<=j<s.len() ==> s.spec_index(i)==s.spec_index(j)
}

fn mallEqual4(v: Vec<int>) -> (b: bool)
    ensures
        b==allEqual(v.spec_index(0..v.len()))
{
    if v.len() == 0 {
        return true;
    }
    
    let first = v[0];
    for i in 1..v.len()
        invariant
            forall j: int :: 0 <= j < i ==> v.spec_index(j) == first,
            0 <= i <= v.len(),
    {
        if v[i as usize] != first {
            return false;
        }
    }
    
    return true;
}

}