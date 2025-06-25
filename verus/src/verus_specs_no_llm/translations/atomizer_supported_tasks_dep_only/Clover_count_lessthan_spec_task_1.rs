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

fn CountLessThan(numbers: set<int>, threshold: int) -> (count: int)
    ensures
        count == set i .len() i in numbers && i < threshold|
{
    return 0;
}

}