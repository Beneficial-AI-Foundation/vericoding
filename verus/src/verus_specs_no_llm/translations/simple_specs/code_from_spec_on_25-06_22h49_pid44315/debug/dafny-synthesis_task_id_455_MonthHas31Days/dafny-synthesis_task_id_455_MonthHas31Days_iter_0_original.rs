// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn MonthHas31Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12
    ensures
        result <==> month in
{
    return false;
}

}