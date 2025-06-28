use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Maximum(values: Seq<int>) -> (max: int)
    requires
        values != Seq::<int>::empty(),
    ensures
        values.contains(max),
        forall|i: int| 0 <= i < values.len() ==> values.spec_index(i) <= max
{
    let mut max = values[0];
    let mut i = 1;
    
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            values.contains(max),
            forall|j: int| 0 <= j < i ==> values.spec_index(j) <= max
    {
        if values[i] > max {
            max = values[i];
        }
        i = i + 1;
    }
    
    max
}

}