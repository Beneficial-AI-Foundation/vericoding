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
proof fn lemma_factorial_monotonic(n: nat, m: nat)
    requires n <= m,
    ensures factorial(n) <= factorial(m)
    decreases m
{
    if n == m {
    } else {
        lemma_factorial_monotonic(n, (m - 1) as nat);
    }
}

proof fn lemma_sum_range_monotonic(n: nat, m: nat)
    requires n <= m,
    ensures sum_range(n) <= sum_range(m)
    decreases m
{
    if n == m {
    } else {
        lemma_sum_range_monotonic(n, (m - 1) as nat);
    }
}

proof fn lemma_factorial_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n > 1 {
        lemma_factorial_positive((n - 1) as nat);
    }
}

proof fn lemma_sum_range_positive(n: nat)
    ensures sum_range(n) >= 0
    decreases n
{
    if n > 0 {
        lemma_sum_range_positive((n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn f(n: u8) -> (result: Vec<u8>)
    ensures valid_result(n as nat, result@.map(|i: int, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed nat/int compilation error by using proper ghost conversion */
    let mut result = Vec::new();
    let mut i: u8 = 0;
    
    while i < n
        invariant
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> 
                (if (j + 1) % 2 == 0 { result@[j] as nat == factorial((j + 1) as nat) }
                 else { result@[j] as nat == sum_range((j + 1) as nat) }),
        decreases (n - i) as int
    {
        proof {
            let ghost_idx = (i + 1) as nat;
            if (i + 1) % 2 == 0 {
                lemma_factorial_positive(ghost_idx);
                lemma_factorial_monotonic(1, ghost_idx);
            } else {
                lemma_sum_range_positive(ghost_idx);
                lemma_sum_range_monotonic(0, ghost_idx);
            }
        }
        
        let value = if (i + 1) % 2 == 0 {
            factorial(((i + 1) as nat)) as u8
        } else {
            sum_range(((i + 1) as nat)) as u8
        };
        
        result.push(value);
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}