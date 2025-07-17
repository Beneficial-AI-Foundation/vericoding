// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsOdd(x: int) -> bool {
    x % 2 != 0
}

spec fn spec_FindFirstOdd(a: Vec<int>) -> found: bool, index: int
    requires
        a != null
    ensures
        !found ==> forall |i: int| 0 <= i < a.len() ==> !IsOdd(a.index(i)),
        found ==> 0 <= index < a.len() && IsOdd(a.index(index)) && forall |i: int| 0 <= i < index ==> !IsOdd(a.index(i))
;

proof fn lemma_FindFirstOdd(a: Vec<int>) -> (found: bool, index: int)
    requires
        a != null
    ensures
        !found ==> forall |i: int| 0 <= i < a.len() ==> !IsOdd(a.index(i)),
        found ==> 0 <= index < a.len() && IsOdd(a.index(index)) && forall |i: int| 0 <= i < index ==> !IsOdd(a.index(i))
{
    (false, 0)
}

}