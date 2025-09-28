// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n <= 1 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn sum_range(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_range((n - 1) as nat) }
}

spec fn valid_result(n: nat, result: Seq<nat>) -> bool
{
    result.len() == n &&
    forall|i: int| 0 <= i < n ==> 
        (if (i + 1) % 2 == 0 { result[i] == factorial((i + 1) as nat) }
         else { result[i] == sum_range((i + 1) as nat) })
}
// </vc-preamble>

// <vc-helpers>
fn compute_factorial(n: nat) -> nat
    decreases n
{
    if n <= 1 {
        1
    } else {
        n * compute_factorial((n - 1) as nat)
    }
}

fn compute_sum_range(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else {
        n + compute_sum_range((n - 1) as nat)
    }
}
// </vc-helpers>

// <vc-spec>
fn f(n: u8) -> (result: Vec<u8>)
    ensures valid_result(n as nat, result@.map(|i: int, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < n as int
        invariant
            0 <= i <= n as int,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (if (j + 1) % 2 == 0 { result[j] as nat == compute_factorial((j + 1) as nat) }
                 else { result[j] as nat == compute_sum_range((j + 1) as nat) }),
        decreases (n as int) - i
    {
        if (i + 1) % 2 == 0 {
            let fact = compute_factorial((i + 1) as nat);
            result.push(fact as u8);
        } else {
            let sum = compute_sum_range((i + 1) as nat);
            result.push(sum as u8);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}