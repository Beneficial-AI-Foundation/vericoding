use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires
        n >= 0
    ensures
        forall i :: 0 <= i < lucid.len() ==> lucid.spec_index(i) % 3 == 0,
        forall i :: 0 <= i < lucid.len() ==> lucid.spec_index(i) <= n,
        forall i, j :: 0 <= i < j < lucid.len() ==> lucid.spec_index(i) < lucid.spec_index(j)
{
    let mut result = Seq::empty();
    let mut current = 0;
    
    while current <= n 
        invariant
            current >= 0,
            current % 3 == 0,
            forall i :: 0 <= i < result.len() ==> result.spec_index(i) % 3 == 0,
            forall i :: 0 <= i < result.len() ==> result.spec_index(i) <= n,
            forall i :: 0 <= i < result.len() ==> result.spec_index(i) < current,
            forall i, j :: 0 <= i < j < result.len() ==> result.spec_index(i) < result.spec_index(j)
    {
        result = result.add(seq![current]);
        current = current + 3;
    }
    
    return result;
}

}