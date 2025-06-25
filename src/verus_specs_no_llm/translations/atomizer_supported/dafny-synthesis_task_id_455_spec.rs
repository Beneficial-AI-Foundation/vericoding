// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn MonthHas31Days(month: int) -> (result: bool)
    requires 1 <= month <= 12
    ensures result <==> month in
{
}

}