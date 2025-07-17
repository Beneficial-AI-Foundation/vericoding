// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn SetProduct(s: set<int>) -> (int)
{
    0
}

spec fn spec_UniqueProduct(arr: Vec<int>) -> product: int
    ensures
        product == SetProduct((set i | 0 <= i < arr.len() :: arr.index(i)))
;

proof fn lemma_UniqueProduct(arr: Vec<int>) -> (product: int)
    ensures
        product == SetProduct((set i | 0 <= i < arr.len() :: arr.index(i)))
{
    0
}

}