// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SubtractSequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) - b.spec_index(i)
{
    let mut result = Seq::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j| 0 <= j < i ==> result.spec_index(j) == a.spec_index(j) - b.spec_index(j)
    {
        result = result.push(a.spec_index(i) - b.spec_index(i));
        i = i + 1;
    }
    
    result
}

}