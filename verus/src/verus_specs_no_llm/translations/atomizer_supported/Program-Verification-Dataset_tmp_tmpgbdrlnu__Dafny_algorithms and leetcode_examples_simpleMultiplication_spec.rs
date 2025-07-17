// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn stringToSet(s: String) -> (r: set<char>)
    ensures
        forall |x: int| 0 <= x < s.len() ==> s.index(x) in r
{
    0
}

spec fn spec_Foo(y: int, x: int) -> z: int
    requires
        0 <= y
    ensures
        z == x*y
;

proof fn lemma_Foo(y: int, x: int) -> (z: int)
    requires
        0 <= y
    ensures
        z == x*y
{
    0
}

}