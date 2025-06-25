// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn UniqueProduct(arr: Vec<int>) -> (product: int)
    ensures product == SetProduct((set i | 0 <= i < arr.len() :: arr[i]))
{
}

}