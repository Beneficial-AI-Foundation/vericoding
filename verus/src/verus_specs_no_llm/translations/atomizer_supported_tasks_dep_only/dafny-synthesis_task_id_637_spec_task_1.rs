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

fn IsBreakEven(costPrice: int, sellingPrice: int) -> (result: bool)
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        result <==> costPrice == sellingPrice
{
    return false;
}

}