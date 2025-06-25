// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn IsBreakEven(costPrice: int, sellingPrice: int) -> (result: bool)
    requires costPrice >= 0 and sellingPrice >= 0
    ensures result <==> costPrice == sellingPrice
{
}

}