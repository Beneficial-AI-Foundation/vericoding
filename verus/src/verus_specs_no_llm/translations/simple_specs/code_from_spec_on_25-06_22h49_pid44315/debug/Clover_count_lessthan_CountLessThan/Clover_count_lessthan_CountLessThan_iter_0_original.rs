// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountLessThan(numbers: set<int>, threshold: int) -> (count: int)
    ensures
        count == set i .len() i in numbers && i < threshold|
{
    return 0;
}

}