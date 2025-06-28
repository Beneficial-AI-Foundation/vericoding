// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn UniqueProduct(arr: Vec<int>) -> (product: int)
    ensures
        product == SetProduct((set i | 0 <= i < arr.len() :: arr.spec_index(i)))
{
    return 0;
}

}