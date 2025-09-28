use vstd::prelude::*;

verus! {

spec fn f(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 }
    else if n % 2 == 0 { 1 + 2 * f(n / 2) }
    else { 2 * f(n / 2) }
}

// <vc-helpers>
proof fn lemma_f_monotonic(n: nat, m: nat)
    requires
        n <= m,
    ensures
        f(n) <= f(m),
    decreases m
{
    if m > n {
        reveal(f);
        if m % 2 == 0 {
            lemma_f_monotonic(n, m / 2);
            assert(f(m) == 1 + 2 * f(m / 2));
            assert(f(n) <= f(m / 2));
        } else {
            lemma_f_monotonic(n, m / 2);
            assert(f(m) == 2 * f(m / 2));
            assert(f(n) <= f(m / 2));
        }
    }
}

spec fn stack_invariant(stack: Vec<u64>, n: nat) -> bool {
    forall|i: int| 0 <= i < stack@.len() ==> stack@[i] as nat <= n
}

spec fn stack_sorted(stack: Vec<u64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < stack@.len() ==> stack@[i] > stack@[j]
}

spec fn stack_measures(stack: Vec<u64>) -> int
{
    stack@.len() as int
}
// </vc-helpers>

// <vc-spec>
fn mod_fn(n: u64) -> (a: u64)
    requires n >= 0,
    ensures a as nat == f(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut a: u64 = 0;
    let mut stack: Vec<u64> = Vec::new();
    let mut current = n;
    
    while current > 0
        invariant
            current >= 0,
            current as nat <= n as nat,
            stack_invariant(stack, n as nat),
            stack_sorted(stack),
        decreases current
    {
        stack.push(current);
        current = current / 2;
    }
    
    a = 1;
    let mut current_nat: nat = 0;
    
    while stack.len() > 0
        invariant
            stack_invariant(stack, n as nat),
            stack_sorted(stack),
            a as nat == f(current_nat),
            current_nat <= n as nat,
        decreases stack_measures(stack)
    {
        let k = stack.pop().unwrap();
        
        proof {
            lemma_f_monotonic(current_nat, n as nat);
        }
        
        if k % 2 == 0 {
            proof {
                assert(current_nat == k as nat / 2) by {
                    reveal(f);
                }
                lemma_f_even(k as nat);
            }
            a = (1 as u64).checked_add(2u64.checked_mul(a).unwrap()).unwrap();
        } else {
            proof {
                assert(current_nat == k as nat / 2) by {
                    reveal(f);
                }
                lemma_f_odd(k as nat);
            }
            a = 2u64.checked_mul(a).unwrap();
        }
        current_nat = k as nat;
    }
    
    a
}
// </vc-code>

fn main() {}

}