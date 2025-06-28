use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxSeq(v: Seq<int>) -> (max: int)
    requires
        v.len() >= 1
    ensures
        forall i :: 0 <= i < v.len() ==> max >= v.spec_index(i),
        max in v
{
    let mut max = v.spec_index(0);
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            max in v,
            forall j :: 0 <= j < i ==> max >= v.spec_index(j)
    {
        if v.spec_index(i) > max {
            max = v.spec_index(i);
        }
        i = i + 1;
    }
    
    max
}

}