// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DogYears(humanYears: int) -> dogYears: int
    requires
        humanYears >= 0
    ensures
        dogYears == 7 * humanYears
;

proof fn lemma_DogYears(humanYears: int) -> (dogYears: int)
    requires
        humanYears >= 0
    ensures
        dogYears == 7 * humanYears
{
    0
}

}