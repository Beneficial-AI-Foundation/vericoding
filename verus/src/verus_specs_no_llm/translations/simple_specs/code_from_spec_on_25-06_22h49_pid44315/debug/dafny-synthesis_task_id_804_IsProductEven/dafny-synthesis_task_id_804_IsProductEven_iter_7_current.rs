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
            assert(IsEven(a.spec_index(i as int))) by {
                assert(a[i] % 2 == 0);
                assert(a.spec_index(i as int) == a[i]);
            }
            assert(0 <= i < a.len());
            assert(exists |k: int| 0 <= k < a.len() && IsEven(a.spec_index(k))) by {
                assert(0 <= i < a.len() && IsEven(a.spec_index(i as int)));
            }
            return true;
        }
        assert(!IsEven(a.spec_index(i as int))) by {
            assert(a[i] % 2 != 0);
            assert(a.spec_index(i as int) == a[i]);
            assert(a.spec_index(i as int) % 2 != 0);
        }
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall |j: int| 0 <= j < a.len() ==> !IsEven(a.spec_index(j)));
    
    assert(!(exists |k: int| 0 <= k < a.len() && IsEven(a.spec_index(k)))) by {
        if exists |k: int| 0 <= k < a.len() && IsEven(a.spec_index(k)) {
            let witness_k = choose |k: int| 0 <= k < a.len() && IsEven(a.spec_index(k));
            assert(0 <= witness_k < a.len() && IsEven(a.spec_index(witness_k)));
            assert(!IsEven(a.spec_index(witness_k)));
            assert(false);
        }
    }
    
    false
}

}