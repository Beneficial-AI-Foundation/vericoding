use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Sum(arr: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        arr[n - 1] + Sum(arr, n - 1)
    }
}

fn SumArray(arr: Vec<int>) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == Sum(arr, i)
    {
        // Need to establish that Sum(arr, i+1) == arr[i] + Sum(arr, i)
        assert(i < arr.len());
        assert(Sum(arr, (i + 1) as nat) == arr[i] + Sum(arr, i as nat));
        
        sum = sum + arr[i];
        i = i + 1;
    }
    
    sum
}

}