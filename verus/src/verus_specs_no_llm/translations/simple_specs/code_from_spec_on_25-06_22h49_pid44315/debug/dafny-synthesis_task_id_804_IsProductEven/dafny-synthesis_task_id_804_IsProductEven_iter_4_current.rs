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
    for i in 0..a.len()
        invariant
            forall |j| 0 <= j < i ==> !IsEven(a.spec_index(j))
    {
        if a[i] % 2 == 0 {
            assert(IsEven(a.spec_index(i)));
            assert(exists |k| 0 <= k < a.len() && IsEven(a.spec_index(k))) by {
                assert(0 <= i < a.len() && IsEven(a.spec_index(i)));
            }
            return true;
        }
        assert(!IsEven(a.spec_index(i)));
    }
    
    assert(forall |j| 0 <= j < a.len() ==> !IsEven(a.spec_index(j)));
    
    assert(!(exists |i| 0 <= i < a.len() && IsEven(a.spec_index(i)))) by {
        if exists |i| 0 <= i < a.len() && IsEven(a.spec_index(i)) {
            let witness_i = choose |i| 0 <= i < a.len() && IsEven(a.spec_index(i));
            assert(0 <= witness_i < a.len() && IsEven(a.spec_index(witness_i)));
            assert(!IsEven(a.spec_index(witness_i)));
            assert(false);
        }
    }
    
    false
}

}