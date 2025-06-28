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
    let mut i: usize = 1;
    
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            exists|j: int| 0 <= j < i ==> max == v.spec_index(j),
            forall|j: int| 0 <= j < i ==> max >= v.spec_index(j)
    {
        if v[i as int] > max {
            max = v[i as int];
        }
        i = i + 1;
    }
    
    max
}

}