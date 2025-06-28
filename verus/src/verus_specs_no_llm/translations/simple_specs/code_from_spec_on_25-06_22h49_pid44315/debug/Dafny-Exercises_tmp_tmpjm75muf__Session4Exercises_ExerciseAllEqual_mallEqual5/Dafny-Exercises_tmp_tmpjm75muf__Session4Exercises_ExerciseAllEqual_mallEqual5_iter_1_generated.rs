use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn allEqual(s: Seq<int>) -> bool {
    forall i,j::0<=i<s.len() && 0<=j<s.len() ==> s.spec_index(i)==s.spec_index(j)
}

fn mallEqual5(v: Vec<int>) -> (b: bool)
    ensures
        b==allEqual(v.spec_index(0..v.len()))
{
    if v.len() == 0 {
        return true;
    }
    
    let first = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall k: int :: 0 <= k < i ==> v.spec_index(k) == first,
    {
        if v[i] != first {
            return false;
        }
        i += 1;
    }
    
    true
}

}