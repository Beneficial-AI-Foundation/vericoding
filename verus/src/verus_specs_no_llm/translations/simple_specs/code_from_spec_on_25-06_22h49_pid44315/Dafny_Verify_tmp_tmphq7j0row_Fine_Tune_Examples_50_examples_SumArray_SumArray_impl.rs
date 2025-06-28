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
        0
    }
}

proof fn lemma_sum_extend(arr: Vec<int>, n: nat)
    requires n < arr.len()
    ensures Sum(arr, n + 1) == arr[n as int] + Sum(arr, n)
{
    assert(n + 1 > 0);
    assert(n + 1 <= arr.len());
    assert(((n + 1) - 1) as int == n as int);
    assert(((n + 1) - 1) as nat == n);
}

fn SumArray(arr: Vec<int>) -> (sum: int)
    requires
        arr.len() > 0
    ensures
        sum == Sum(arr, arr.len())
{
    let mut sum = 0;
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            sum == Sum(arr, i as nat)
    {
        assert(i < arr.len());
        
        proof {
            lemma_sum_extend(arr, i as nat);
        }
        
        sum = sum + arr[i as int];
        i = i + 1;
    }
    
    sum
}

}