use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountIdenticalPositions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: int)
    requires
        a.len() == b.len() && b.len() == c.len()
    ensures
        count >= 0,
        count == (set|i: int| 0 <= i < a.len() && a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i)).len()
{
    let mut count = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count >= 0,
            count == (set|j: int| 0 <= j < i && a.spec_index(j) == b.spec_index(j) && b.spec_index(j) == c.spec_index(j)).len(),
            a.len() == b.len() && b.len() == c.len()
    {
        if a.spec_index(i) == b.spec_index(i) && b.spec_index(i) == c.spec_index(i) {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

}