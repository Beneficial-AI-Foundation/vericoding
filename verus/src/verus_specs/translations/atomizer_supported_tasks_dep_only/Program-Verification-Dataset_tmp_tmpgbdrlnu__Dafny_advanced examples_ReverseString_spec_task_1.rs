use vstd::prelude::*;

verus! {

spec fn reversed(arr: &[char], outarr: &[char]) -> bool {
    arr.len() == outarr.len() &&
    forall|k: int| 0 <= k < arr.len() ==> outarr[k] == arr[(arr.len() - 1 - k) as int]
}

pub fn yarra(arr: &[char]) -> (outarr: Vec<char>)
    requires(arr.len() > 0)
    ensures(arr.len() == outarr.len() && reversed(arr, &outarr))
{
    todo!()
}

}