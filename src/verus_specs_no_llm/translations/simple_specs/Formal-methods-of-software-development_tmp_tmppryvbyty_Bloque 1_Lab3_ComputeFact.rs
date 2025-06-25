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

fn ComputeFact(n: int) -> (f: int)
    requires
        n >=0
    ensures
        f== factorial(n)
{
    return 0;
}

}