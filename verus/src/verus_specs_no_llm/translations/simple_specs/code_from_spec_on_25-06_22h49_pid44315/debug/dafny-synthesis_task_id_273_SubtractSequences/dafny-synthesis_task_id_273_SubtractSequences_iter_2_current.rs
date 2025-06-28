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
        forall |i: int| 0 <= i < result.len() ==> result[i] == a[i] - b[i]
{
    let mut result: Seq<int> = Seq::empty();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |j: int| 0 <= j < i ==> result[j] == a[j] - b[j]
    {
        result = result.push(a[i as int] - b[i as int]);
        i = i + 1;
    }
    
    result
}

}