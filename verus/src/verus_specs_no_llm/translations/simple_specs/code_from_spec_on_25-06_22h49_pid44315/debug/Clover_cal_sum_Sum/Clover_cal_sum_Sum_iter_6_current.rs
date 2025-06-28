use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Sum(N: int) -> (s: int)
    requires
        N >= 0
    ensures
        s == N * (N + 1) / 2
{
    let mut i: int = 0;
    let mut sum: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            sum == i * (i + 1) / 2
    {
        i = i + 1;
        sum = sum + i;
        
        // Proof assertion to help Verus verify the invariant
        assert(sum == i * (i + 1) / 2) by {
            // The sum after adding i is: old_sum + i = (i-1)*i/2 + i
            // We need to show this equals i*(i+1)/2
            // (i-1)*i/2 + i = (i-1)*i/2 + 2*i/2 = ((i-1)*i + 2*i)/2 = (i*i - i + 2*i)/2 = (i*i + i)/2 = i*(i+1)/2
        }
    }
    
    sum
}

}