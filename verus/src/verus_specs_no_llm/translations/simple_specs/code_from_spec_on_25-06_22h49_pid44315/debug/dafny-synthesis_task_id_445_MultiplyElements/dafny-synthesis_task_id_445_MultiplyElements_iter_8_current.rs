use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MultiplyElements(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result.spec_index(i) == a.spec_index(i) * b.spec_index(i)
{
    let mut result = seq![];
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < result.len() ==> result.spec_index(j) == a.spec_index(j) * b.spec_index(j)
    {
        let product = a[i as int] * b[i as int];
        result = result.push(product);
        i = i + 1;
    }
    
    result
}

}