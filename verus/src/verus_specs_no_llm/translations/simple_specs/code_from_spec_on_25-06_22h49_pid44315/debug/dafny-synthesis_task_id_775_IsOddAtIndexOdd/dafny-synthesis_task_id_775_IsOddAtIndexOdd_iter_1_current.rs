use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(n: int) -> bool {
    n % 2 == 1
}

fn IsOddAtIndexOdd(a: Vec<int>) -> (result: bool)
    ensures
        result <==> forall |i: int| 0 <= i < a.len() ==> (IsOdd(i) ==> IsOdd(a.spec_index(i)))
{
    let mut i: usize = 1; // Start with the first odd index
    
    while i < a.len()
        invariant
            i % 2 == 1, // i is always odd
            forall |j: int| 0 <= j < i ==> (IsOdd(j) ==> IsOdd(a.spec_index(j))),
    {
        if !IsOdd(a[i] as int) {
            return false;
        }
        i += 2; // Move to next odd index
    }
    
    true
}

}