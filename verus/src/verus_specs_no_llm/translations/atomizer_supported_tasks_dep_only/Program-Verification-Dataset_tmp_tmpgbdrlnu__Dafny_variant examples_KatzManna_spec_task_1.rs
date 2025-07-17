// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> z: int
    ensures
        proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
;

proof fn lemma_NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> (z: int)
    ensures
        proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
{
    0
}

}