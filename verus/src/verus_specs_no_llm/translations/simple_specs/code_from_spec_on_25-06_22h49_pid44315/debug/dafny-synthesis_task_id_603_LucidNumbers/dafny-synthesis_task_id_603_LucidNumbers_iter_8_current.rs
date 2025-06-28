use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LucidNumbers(n: int) -> (lucid: Seq<int>)
    requires
        n >= 0
    ensures
        forall|i: int| 0 <= i < lucid.len() ==> lucid.spec_index(i) % 3 == 0,
        forall|i: int| 0 <= i < lucid.len() ==> lucid.spec_index(i) <= n,
        forall|i: int, j: int| 0 <= i < j < lucid.len() ==> lucid.spec_index(i) < lucid.spec_index(j)
{
    let mut result = Seq::empty();
    let mut current = 0int;
    
    while current <= n 
        invariant
            current >= 0,
            current % 3 == 0,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) % 3 == 0,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) < current,
            forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) <= n,
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result.spec_index(i) < result.spec_index(j),
            forall|k: int| 0 <= k < current && k % 3 == 0 ==> exists|i: int| 0 <= i < result.len() && result.spec_index(i) == k
        decreases n - current
    {
        result = result.push(current);
        current = current + 3;
    }
    
    result
}

}