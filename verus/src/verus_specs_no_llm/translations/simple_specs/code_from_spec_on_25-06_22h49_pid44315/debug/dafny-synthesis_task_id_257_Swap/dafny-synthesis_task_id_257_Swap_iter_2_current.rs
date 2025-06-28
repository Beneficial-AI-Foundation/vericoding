use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Swap(a: int, b: int) -> (result: Seq<int>)
    ensures
        result.len() == 2,
        result.spec_index(0) == b,
        result.spec_index(1) == a
{
    let result = seq![b, a];
    
    // Proof annotations to help Verus verify the postconditions
    assert(result.len() == 2);
    assert(result.spec_index(0) == b);
    assert(result.spec_index(1) == a);
    
    result
}

}