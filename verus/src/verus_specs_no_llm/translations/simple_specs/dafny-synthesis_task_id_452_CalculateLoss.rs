// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CalculateLoss(costPrice: int, sellingPrice: int) -> loss: int
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
;

proof fn lemma_CalculateLoss(costPrice: int, sellingPrice: int) -> (loss: int)
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        (costPrice > sellingPrice ==> loss == costPrice - sellingPrice) && (costPrice <= sellingPrice ==> loss == 0)
{
    0
}

}