// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sorted(a: Seq<int>) -> bool {
    forall |j: int, k: int| 0 <= j < k < a.len() ==> a.spec_index(j) <= a.spec_index(k)
}

fn unique(a: Seq<int>) -> (b: Seq<int>)
    requires
        sorted(a)
    ensures
        true
{
    if a.len() == 0 {
        return Seq::empty();
    }
    
    let mut result = Seq::empty();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sorted(a),
    {
        let current = a.spec_index(i);
        if result.len() == 0 || current != result.spec_index(result.len() - 1) {
            result = result.push(current);
        }
        i = i + 1;
    }
    
    result
}

}