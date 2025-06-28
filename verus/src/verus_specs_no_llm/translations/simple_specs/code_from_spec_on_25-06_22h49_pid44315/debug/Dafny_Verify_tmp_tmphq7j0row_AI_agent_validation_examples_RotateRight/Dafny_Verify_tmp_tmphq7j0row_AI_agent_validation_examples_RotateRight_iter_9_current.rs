use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Specification function for power
spec fn Power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * Power(n - 1) }
}

// Find maximum value in a vector
fn Max(a: Vec<nat>) -> (m: int)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> a[i] as int <= m
    ensures exists|i: int| 0 <= i < a.len() && m == a[i] as int
{
    let mut m = a[0] as int;
    let mut idx = 1;
    
    while idx < a.len()
        invariant 1 <= idx <= a.len()
        invariant forall|i: int| 0 <= i < idx ==> a[i] as int <= m
        invariant exists|i: int| 0 <= i < idx && m == a[i] as int
        invariant a.len() > 0
    {
        if a[idx] as int > m {
            m = a[idx] as int;
        }
        idx = idx + 1;
    }
    m
}

// Compute cube of a natural number
fn Cube(n: nat) -> (c: nat)
    ensures c == n * n * n
{
    n * n * n
}

// Double each element in source array and store in destination
fn DoubleArray(src: &Vec<int>, dst: &mut Vec<int>)
    requires src.len() == dst.len()
    ensures src.len() == dst.len()
    ensures forall|i: int| 0 <= i < src.len() ==> dst[i] == 2 * src[i]
{
    let mut idx = 0;
    
    while idx < src.len()
        invariant 0 <= idx <= src.len()
        invariant src.len() == dst.len()
        invariant forall|i: int| 0 <= i < idx ==> dst[i] == 2 * src[i]
    {
        dst.set(idx, 2 * src[idx]);
        idx = idx + 1;
    }
}

// Helper proof function to establish the Power relationship
proof fn power_step_lemma(count: nat)
    ensures Power(count + 1) == 2 * Power(count)
{
    // The proof follows directly from the definition of Power
}

// Compute power using the Power specification function
fn ComputePower(N: int) -> (y: nat)
    requires N >= 0
    ensures y == Power(N as nat)
{
    if N == 0 {
        1
    } else {
        let mut result: nat = 1;
        let mut count = 0;
        
        while count < N
            invariant 0 <= count <= N
            invariant result == Power(count as nat)
        {
            proof {
                power_step_lemma(count as nat);
            }
            result = result * 2;
            count = count + 1;
        }
        result
    }
}

}