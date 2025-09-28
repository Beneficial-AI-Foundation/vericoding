use vstd::prelude::*;

verus! {

/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).

// <vc-helpers>
// Lemma showing that x^i * x^j = x^(i+j)
proof fn power_add_exponents(x: int, i: nat, j: nat)
    ensures power(x, i) * power(x, j) == power(x, (i + j) as nat)
    decreases i
{
    if i == 0 {
        // power(x, 0) = 1 by definition
        // 1 * power(x, j) = power(x, j)
        // power(x, 0 + j) = power(x, j)
        assert(power(x, 0) == 1);
        assert(power(x, (0 + j) as nat) == power(x, j));
    } else {
        // Recursive case: prove that x^i * x^j = x^(i+j)
        // We know power(x, i) = x * power(x, i-1)
        power_add_exponents(x, (i - 1) as nat, j);
        // By induction hypothesis: power(x, i-1) * power(x, j) = power(x, (i-1)+j)
        
        // power(x, i) * power(x, j) 
        // = x * power(x, i-1) * power(x, j)
        // = x * power(x, (i-1)+j)
        // = power(x, 1 + (i-1)+j)
        // = power(x, i+j)
        
        assert(power(x, i) == x * power(x, (i - 1) as nat)); // By definition
        assert(power(x, (i - 1) as nat) * power(x, j) == power(x, ((i - 1) + j) as nat)); // By IH
        assert(power(x, i) * power(x, j) == x * power(x, (i - 1) as nat) * power(x, j));
        assert(x * power(x, ((i - 1) + j) as nat) == power(x, (1 + (i - 1) + j) as nat));
        assert((1 + (i - 1) + j) as nat == (i + j) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn power_iter(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result: i64 = 1;
    let mut i: u64 = 0;
    
    while i < n
        invariant
            i <= n,
            result == power(x as int, i as nat),
        decreases n - i
    {
        let old_i = i;
        let old_result = result;
        
        i = i + 1;
        result = result * x;
        
        proof {
            // We need to show that result == power(x, i)
            // After the updates: result = old_result * x and i = old_i + 1
            // old_result == power(x, old_i) by the loop invariant
            // So result = power(x, old_i) * x
            // We need to show this equals power(x, old_i + 1)
            
            assert(old_result == power(x as int, old_i as nat));
            assert(result == old_result * x);
            assert(i == old_i + 1);
            
            // By definition of power: power(x, old_i + 1) = x * power(x, old_i)
            assert(power(x as int, (old_i + 1) as nat) == x * power(x as int, old_i as nat));
            assert(result == power(x as int, old_i as nat) * x);
            assert(result == x * power(x as int, old_i as nat));
            assert(result == power(x as int, (old_i + 1) as nat));
            assert(result == power(x as int, i as nat));
        }
    }
    
    result
}
// </vc-code>

// Recursive version, imperative, with time and space complexity O(log n).

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.

// A simple test case to make sure the specification is adequate.

fn main() {
}

}