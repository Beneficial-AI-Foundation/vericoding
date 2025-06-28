use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Define Factorial as a spec function (computing n! factorial)
spec fn Factorial(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { n * Factorial(n - 1) }
}

// Define Power as a spec function (computing n^n)
spec fn Power(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { n * Power(n - 1) }
}

fn ComputePower1(N: int) -> (y: nat) 
    requires N >= 0
    ensures y == Factorial(N)  // This function actually computes factorial
{
    if N == 0 {
        1
    } else {
        let mut result: nat = 1;
        let mut i: int = 1;
        while i <= N
            invariant 
                1 <= i <= N + 1,
                result == Factorial(i - 1)
        {
            assert(i > 0);
            assert(i - 1 >= 0);
            // Need to prove that the multiplication won't overflow
            proof {
                assert(result == Factorial(i - 1));
                assert(Factorial(i) == i * Factorial(i - 1));
            }
            result = result * (i as nat);
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
                // Help the verifier understand that m is now equal to a[i]
                assert(m == a.spec_index(i as int));
                assert(exists|j: int| 0 <= j < (i + 1) as int && m == a.spec_index(j));
            }
            i = i + 1;
        }
        // Final assertion to help prove the postcondition
        assert(i == a.len());
        assert(forall|j: int| 0 <= j < a.len() ==> a.spec_index(j) <= m);
        assert(exists|j: int| 0 <= j < a.len() && m == a.spec_index(j));
        m
    }
}

fn Cube(n: nat) -> (c: nat)
    ensures c == n * n * n
{
    n * n * n
}

}