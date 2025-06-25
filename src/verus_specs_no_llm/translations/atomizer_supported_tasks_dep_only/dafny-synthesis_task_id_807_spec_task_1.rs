// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

fn FindFirstOdd(a: Vec<int>) -> (found: bool, index: int)
    requires
        a != null
    ensures
        !found ==> forall i :: 0 <= i < a.len() ==> !IsOdd(a.spec_index(i)),
        found ==> 0 <= index < a.len() && IsOdd(a.spec_index(index)) && forall i :: 0 <= i < index ==> !IsOdd(a.spec_index(i))
{
    return (false, 0);
}

}