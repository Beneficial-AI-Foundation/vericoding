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
    let mut i: usize = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            0 <= sum,
            0 <= max,
            sum <= i * max,
            forall k :: 0 <= k < i ==> a.spec_index(k) <= max,
            forall k :: 0 <= k < i ==> sum >= a.spec_index(k)
    {
        let current = a[i];
        sum = sum + current;
        if current > max {
            max = current;
        }
        i = i + 1;
    }
    
    (sum, max)
}

}