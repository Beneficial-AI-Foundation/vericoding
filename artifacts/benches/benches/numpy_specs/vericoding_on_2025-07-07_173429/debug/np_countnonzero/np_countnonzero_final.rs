use vstd::prelude::*;

verus! {

fn nonzero(arr: &[i32]) -> (num: usize)
    requires 
        arr.len() >= 0,
    ensures 
        num >= 0,
        num <= arr.len(),
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