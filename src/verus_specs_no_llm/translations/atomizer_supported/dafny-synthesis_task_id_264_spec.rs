// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn DogYears(humanYears: int) -> (dogYears: int)
    requires humanYears >= 0
    ensures dogYears == 7 * humanYears
{
}

}