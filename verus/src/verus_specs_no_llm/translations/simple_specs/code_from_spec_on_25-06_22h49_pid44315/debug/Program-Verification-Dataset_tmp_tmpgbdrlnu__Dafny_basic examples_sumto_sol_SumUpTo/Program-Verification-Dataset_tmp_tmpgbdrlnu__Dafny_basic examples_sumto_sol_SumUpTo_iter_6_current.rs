use builtin::*;
use builtin_macros::*;

verus! {

spec fn sum_up_to(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        sum_up_to(n - 1) + (n - 1)
    }
}

proof fn sum_up_to_step(i: nat)
    ensures sum_up_to(i + 1) == sum_up_to(i) + i
{
    // The proof follows from the definition of sum_up_to
    // sum_up_to(i + 1) = sum_up_to((i + 1) - 1) + ((i + 1) - 1)
    //                  = sum_up_to(i) + i
}

fn SumUpTo(n: nat) -> (r: nat)
    ensures
        r == sum_up_to(n)
{
    let mut i: nat = 0;
    let mut sum: nat = 0;
    
    while i < n
        invariant
            i <= n,
            sum == sum_up_to(i),
        decreases n - i
    {
        proof {
            sum_up_to_step(i);
        }
        sum = sum + i;
        i = i + 1;
    }
    
    sum
}

fn main() {
}

}

The code should now verify correctly. The key elements are: