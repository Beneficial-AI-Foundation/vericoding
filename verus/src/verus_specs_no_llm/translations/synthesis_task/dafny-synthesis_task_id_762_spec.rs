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

fn IsMonthWith30Days(month: int) -> (result: bool)
    requires
        1 <= month <= 12
    ensures
        result <==> month == 4 | month == 6 .len() month == 9 .len()| month == 11
{
    return false;
}

}