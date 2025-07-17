// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsGreater(n: int, a: Vec<int>) -> result: bool
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() ==> n > a.index(i),
        !result ==> exists |i: int| 0 <= i < a.len() && n <= a.index(i)
;

proof fn lemma_IsGreater(n: int, a: Vec<int>) -> (result: bool)
    requires
        a != null
    ensures
        result ==> forall |i: int| 0 <= i < a.len() ==> n > a.index(i),
        !result ==> exists |i: int| 0 <= i < a.len() && n <= a.index(i)
{
    false
}

}