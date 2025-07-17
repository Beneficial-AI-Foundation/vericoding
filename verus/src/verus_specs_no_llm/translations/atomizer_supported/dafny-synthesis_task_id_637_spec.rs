// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsBreakEven(costPrice: int, sellingPrice: int) -> result: bool
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        result <==> costPrice == sellingPrice
;

proof fn lemma_IsBreakEven(costPrice: int, sellingPrice: int) -> (result: bool)
    requires
        costPrice >= 0 && sellingPrice >= 0
    ensures
        result <==> costPrice == sellingPrice
{
    false
}

}