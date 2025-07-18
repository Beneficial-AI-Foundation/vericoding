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

proof fn lemma_sum_extend(arr: Vec<int>, n: nat)
    requires n < arr.len()
    ensures Sum(arr, n + 1) == arr[n as int] + Sum(arr, n)
{
    // The proof follows from the definition of Sum
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
            sum == Sum(arr, i as nat)
    {
        proof {
            lemma_sum_extend(arr, i as nat);
        }
        
        sum = sum + arr[i as int];
        i = i + 1;
    }
    
    sum
}

}