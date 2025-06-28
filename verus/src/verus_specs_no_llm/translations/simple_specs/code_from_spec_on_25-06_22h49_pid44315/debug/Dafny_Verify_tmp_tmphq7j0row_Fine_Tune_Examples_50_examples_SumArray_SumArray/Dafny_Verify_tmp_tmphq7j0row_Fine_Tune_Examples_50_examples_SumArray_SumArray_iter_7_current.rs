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
    } else if n <= arr.len() {
        arr[(n - 1) as int] + Sum(arr, (n - 1) as nat)
    } else {
        0  // Handle out-of-bounds case
    }
}

proof fn lemma_sum_extend(arr: Vec<int>, n: nat)
    requires n < arr.len()
    ensures Sum(arr, n + 1) == arr[n as int] + Sum(arr, n)
{
    // The proof follows from the definition of Sum
    // Since n < arr.len(), we have n + 1 <= arr.len()
    // So Sum(arr, n + 1) expands to arr[n] + Sum(arr, n)
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
            assert(i < arr.len());
            assert((i as nat) < arr.len());
            lemma_sum_extend(arr, i as nat);
            assert(Sum(arr, (i as nat) + 1) == arr[i as int] + Sum(arr, i as nat));
        }
        
        sum = sum + arr[i as int];
        i = i + 1;
        
        proof {
            assert(sum == arr[(i - 1) as int] + Sum(arr, (i - 1) as nat));
            assert((i - 1) as nat + 1 == i as nat);
            assert(Sum(arr, i as nat) == arr[(i - 1) as int] + Sum(arr, (i - 1) as nat));
        }
    }
    
    sum
}

}