use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        a[n as int - 1] + sumTo(a, (n - 1) as nat)
    }
}

fn sum_array(a: Vec<int>) -> (sum: int)
    ensures
        sum == sumTo(a, a.len())
{
    let mut sum = 0;
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum == sumTo(a, i)
    {
        sum = sum + a[i as int];
        i = i + 1;
    }
    
    sum
}

}