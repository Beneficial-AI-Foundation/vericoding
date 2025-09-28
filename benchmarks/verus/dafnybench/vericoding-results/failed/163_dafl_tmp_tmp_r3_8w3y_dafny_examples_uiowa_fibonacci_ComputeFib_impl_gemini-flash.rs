use vstd::prelude::*;

verus! {

/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa

   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/


//      n = 0, 1, 2, 3, 4, 5, 6,  7,  8, ...
// fib(n) = 0, 1, 1, 2, 3, 5, 8, 13, 21, ...
spec fn fib(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib((n - 1) as nat) + fib((n - 2) as nat) }
}

// <vc-helpers>
spec fn fib_helper(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else { fib_helper((n - 1) as nat) + fib_helper((n - 2) as nat) }
}
// </vc-helpers>

// <vc-spec>
fn ComputeFib(n: usize) -> (f: usize)
    ensures f == fib(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        let mut i: usize = 2;
        let mut f_i_minus_1: usize = 1;
        let mut f_i_minus_2: usize = 0;
        let mut f_i: usize = 1;

        while i <= n
            invariant
                2 <= i,
                i <= n + 1,
                f_i_minus_2 == fib_helper((i - 2) as nat),
                f_i_minus_1 == fib_helper((i - 1) as nat),
                f_i == fib_helper(i as nat),
            decreases (n - i) as int
        {
            f_i_minus_2 = f_i_minus_1;
            f_i_minus_1 = f_i;
            f_i = f_i_minus_1 + f_i_minus_2;
            i = i + 1;
        }
        f_i
    }
}
// </vc-code>

fn main() {
}

}