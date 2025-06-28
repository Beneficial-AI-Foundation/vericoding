use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to count true values up to index i
spec fn countTo(a: Vec<bool>, i: int) -> int
    decreases i
{
    if i <= 0 {
        0
    } else if i >= a.len() {
        countTo(a, a.len() - 1) + if a[a.len() - 1] { 1 } else { 0 }
    } else {
        countTo(a, i - 1) + if a[i - 1] { 1 } else { 0 }
    }
}

fn CountTrue(a: Vec<bool>) -> (result: usize)
    ensures
        result == countTo(a, a.len() as int)
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            count == countTo(a, i as int)
    {
        if a[i] {
            count = count + 1;
        }
        i = i + 1;
    }
    
    count
}

fn main() {
}

}