// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) -> (z: int)
    ensures
        proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91
{
    return 0;
}

}