use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn maxSeq(v: Seq<int>) -> (max: int)
    requires
        v.len() >= 1
    ensures
        forall|i: int| 0 <= i < v.len() ==> max >= v.spec_index(i),
        exists|i: int| 0 <= i < v.len() && max == v.spec_index(i)
{
    let mut max = v[0];
    let mut i = 1;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            exists|j: int| 0 <= j < v.len() && max == v.spec_index(j),
            forall|j: int| 0 <= j < i ==> max >= v.spec_index(j)
    {
        if v[i as usize] > max {
            max = v[i as usize];
        }
        i = i + 1;
    }
    
    max
}

}