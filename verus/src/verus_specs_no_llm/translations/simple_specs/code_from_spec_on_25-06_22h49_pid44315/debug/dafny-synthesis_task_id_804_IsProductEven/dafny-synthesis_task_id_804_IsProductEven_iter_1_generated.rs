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
            return true;
        }
    }
    false
}

}