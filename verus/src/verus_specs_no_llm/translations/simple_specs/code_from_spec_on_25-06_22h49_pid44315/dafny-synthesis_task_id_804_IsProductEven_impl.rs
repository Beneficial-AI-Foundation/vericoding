use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsEven(n: int) -> bool {
    n % 2 == 0
}

fn IsProductEven(a: Vec<int>) -> (result: bool)
    ensures
        result <==> exists |i| 0 <= i < a.len() && IsEven(a.spec_index(i))
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall |j: int| 0 <= j < i ==> !IsEven(a.spec_index(j))
    {
        if a[i] % 2 == 0 {
            assert(IsEven(a.spec_index(i as int)));
            assert(0 <= i < a.len());
            return true;
        }
        i = i + 1;
    }
    
    // When we exit the loop, we've checked all elements and none are even
    assert(i == a.len());
    assert(forall |j: int| 0 <= j < a.len() ==> !IsEven(a.spec_index(j)));
    
    // This directly implies that there exists no even element
    assert(!(exists |k| 0 <= k < a.len() && IsEven(a.spec_index(k)))) by {
        if exists |k| 0 <= k < a.len() && IsEven(a.spec_index(k)) {
            let k = choose |k| 0 <= k < a.len() && IsEven(a.spec_index(k));
            assert(0 <= k < a.len());
            assert(IsEven(a.spec_index(k)));
            assert(!IsEven(a.spec_index(k))); // contradiction
            assert(false);
        }
    }
    
    false
}

}