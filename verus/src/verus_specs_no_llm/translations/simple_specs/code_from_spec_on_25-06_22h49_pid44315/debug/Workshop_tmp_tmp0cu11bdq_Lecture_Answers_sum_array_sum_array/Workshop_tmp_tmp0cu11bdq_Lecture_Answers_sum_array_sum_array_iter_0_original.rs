// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn sum_array(a: Vec<int>) -> (sum: int)
    requires
        a != null
    ensures
        sum == sumTo(a, a.len())
{
    return 0;
}

}