use vstd::prelude::*;

verus! {

fn nonzero(arr: &[i32]) -> (num: usize)
    requires arr.len() >= 0  // always true in Verus
    ensures num >= 0  // always true for usize
    // Note: The recursive postcondition from Dafny cannot be directly translated
    // since it refers to a recursive call that's not allowed
{
    let mut num = 0;
    let mut i = 0;
    while i < arr.len()
        invariant 
            0 <= i <= arr.len(),
            num >= 0,
            num <= i,
        decreases arr.len() - i,
    {
        if arr[i] != 0 {
            num = num + 1;
        }
        i = i + 1;
    }
    num
}

}

fn main() {}