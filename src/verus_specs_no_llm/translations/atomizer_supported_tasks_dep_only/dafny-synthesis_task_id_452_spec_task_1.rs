// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CalculateLoss(costPrice: int, sellingPrice: int) -> (loss: int)
    requires costPrice >= 0 and sellingPrice >= 0
    ensures (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) and (costPrice <= sellingPrice ==> loss == 0)
{
}

}