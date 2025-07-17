// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountLessThan(numbers: set<int>, threshold: int) -> count: int
    ensures
        count == set i .len() i in numbers && i < threshold|
;

proof fn lemma_CountLessThan(numbers: set<int>, threshold: int) -> (count: int)
    ensures
        count == set i .len() i in numbers && i < threshold|
{
    0
}

}