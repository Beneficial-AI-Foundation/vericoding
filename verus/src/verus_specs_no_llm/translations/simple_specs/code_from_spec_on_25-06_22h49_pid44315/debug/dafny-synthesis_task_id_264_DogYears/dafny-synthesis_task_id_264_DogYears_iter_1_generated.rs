// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn DogYears(humanYears: int) -> (dogYears: int)
    requires
        humanYears >= 0
    ensures
        dogYears == 7 * humanYears
{
    return 7 * humanYears;
}

}