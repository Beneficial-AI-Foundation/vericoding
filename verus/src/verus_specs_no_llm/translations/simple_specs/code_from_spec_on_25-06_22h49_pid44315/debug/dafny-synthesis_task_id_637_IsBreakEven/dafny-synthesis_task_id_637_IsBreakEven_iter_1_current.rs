// Translated from Dafny
use builtin::*;
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
    costPrice == sellingPrice
}

}