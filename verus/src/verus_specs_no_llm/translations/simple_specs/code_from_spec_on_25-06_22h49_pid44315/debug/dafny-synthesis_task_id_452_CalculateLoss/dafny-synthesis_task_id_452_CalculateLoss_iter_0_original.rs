// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalculateLoss(costPrice: int, sellingPrice: int) -> (loss: int)
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
    return 0;
}

}