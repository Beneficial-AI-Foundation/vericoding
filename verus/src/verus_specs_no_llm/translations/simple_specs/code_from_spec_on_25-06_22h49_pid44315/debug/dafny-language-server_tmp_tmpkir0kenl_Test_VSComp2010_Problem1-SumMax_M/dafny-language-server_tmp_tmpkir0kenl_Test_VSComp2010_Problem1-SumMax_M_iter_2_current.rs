use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn M(N: int, a: Vec<int>) -> (sum: int, max: int)
    requires
        0 <= N && a.len() == N && (forall k :: 0 <= k && k < N ==> 0 <= a.spec_index(k))
    ensures
        sum <= N * max
{
    if N == 0 {
        return (0, 0);
    }
    
    let mut sum: int = 0;
    let mut max: int = 0;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            0 <= sum,
            0 <= max,
            sum <= i * max,
            forall k :: 0 <= k < i ==> a.spec_index(k) <= max,
            sum == (spec_sum(a, i))
        decreases N - i
    {
        let current = a[i as usize];
        sum = sum + current;
        if current > max {
            max = current;
        }
        i = i + 1;
    }
    
    (sum, max)
}

spec fn spec_sum(a: Vec<int>, n: int) -> int
    decreases n
{
    if n <= 0 {
        0
    } else {
        spec_sum(a, n - 1) + a.spec_index(n - 1)
    }
}

}