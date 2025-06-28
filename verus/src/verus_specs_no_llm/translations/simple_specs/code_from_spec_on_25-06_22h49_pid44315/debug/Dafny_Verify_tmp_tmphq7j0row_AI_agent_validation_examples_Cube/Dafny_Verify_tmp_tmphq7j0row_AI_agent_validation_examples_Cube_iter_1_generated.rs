use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define Power as a spec function first
spec fn Power(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { n * Power(n - 1) }
}

fn ComputePower1(N: int) -> (y: nat) 
    requires N >= 0
    ensures y == Power(N)
{
    if N == 0 {
        1
    } else {
        let mut result: nat = 1;
        let mut i: int = 0;
        while i < N
            invariant 
                0 <= i <= N,
                result == Power(i)
        {
            result = result * (N as nat);
            i = i + 1;
        }
        result
    }
}

fn Max(a: &Vec<nat>) -> (m: nat)
    ensures forall|i: int| 0 <= i < a.len() ==> a.spec_index(i) <= m
    ensures (m == 0 && a.len() == 0) || exists|i: int| 0 <= i < a.len() && m == a.spec_index(i)
{
    if a.len() == 0 {
        0
    } else {
        let mut m: nat = a[0];
        let mut i: usize = 1;
        
        while i < a.len()
            invariant
                1 <= i <= a.len(),
                forall|j: int| 0 <= j < i ==> a.spec_index(j) <= m,
                exists|j: int| 0 <= j < i && m == a.spec_index(j)
        {
            if a[i] > m {
                m = a[i];
            }
            i = i + 1;
        }
        m
    }
}

fn Cube(n: nat) -> (c: nat)
    ensures c == n * n * n
{
    n * n * n
}

}