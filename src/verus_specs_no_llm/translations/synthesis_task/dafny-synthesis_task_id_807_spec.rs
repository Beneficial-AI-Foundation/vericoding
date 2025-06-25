// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

fn FindFirstOdd(a: Vec<int>) -> found: bool, index: int
    requires a != null
    ensures !found ==> forall|i: int| 0 <= i < a.len() ==> !IsOdd(a[i]),
            found ==> 0 <= index < a.len() and IsOdd(a[index]) and forall|i: int| 0 <= i < index ==> !IsOdd(a[i])
{
}

}