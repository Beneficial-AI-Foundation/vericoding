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
        assert(!IsEven(a.spec_index(i as int)));
        i = i + 1;
    }
    
    assert(i == a.len());
    assert(forall |j: int| 0 <= j < a.len() ==> !IsEven(a.spec_index(j)));
    
    false
}

}