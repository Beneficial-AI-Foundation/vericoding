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
/* helper modified by LLM (iteration 5): Fixed factorial bound lemma assertions and sum_range bound calculation */
proof fn factorial_bound_lemma(n: nat)
    ensures n <= 5 ==> factorial(n) <= 120
    decreases n
{
    if n <= 1 {
        assert(factorial(n) == 1);
    } else if n == 2 {
        assert(factorial(1) == 1);
        assert(factorial(2) == 2 * factorial(1));
        assert(factorial(2) == 2);
    } else if n == 3 {
        factorial_bound_lemma(2);
        assert(factorial(2) == 2);
        assert(factorial(3) == 3 * factorial(2));
        assert(factorial(3) == 6);
    } else if n == 4 {
        factorial_bound_lemma(3);
        assert(factorial(3) == 6);
        assert(factorial(4) == 4 * factorial(3));
        assert(factorial(4) == 24);
    } else if n == 5 {
        factorial_bound_lemma(4);
        assert(factorial(4) == 24);
        assert(factorial(5) == 5 * factorial(4));
        assert(factorial(5) == 120);
    }
}

proof fn sum_range_bound_lemma(n: nat)
    ensures n <= 255 ==> sum_range(n) <= 32640
    decreases n
{
    if n == 0 {
        assert(sum_range(0) == 0);
    } else if n <= 255 {
        sum_range_bound_lemma((n - 1) as nat);
        assert(sum_range(n) == n + sum_range((n - 1) as nat));
        assert(sum_range(n) <= n + 32640 - n + 1);
        assert(sum_range(n) <= 32640);
    }
}
// </vc-helpers>

// <vc-spec>
fn f(n: u8) -> (result: Vec<u8>)
    ensures valid_result(n as nat, result@.map(|i: int, x: u8| x as nat))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed overflow issues and loop invariants */
    let mut result = Vec::new();
    let mut i: u8 = 0;
    
    while i < n
        invariant
            i <= n,
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> 
                (if (j + 1) % 2 == 0 { result@[j] as nat == factorial((j + 1) as nat) % 256 }
                 else { result@[j] as nat == sum_range((j + 1) as nat) % 256 })
        decreases n - i
    {
        let val = if (i + 1) % 2 == 0 {
            // Factorial case
            let mut f: u8 = 1;
            let mut k: u8 = 1;
            
            if i + 1 <= 5 {
                proof { factorial_bound_lemma((i + 1) as nat); }
                while k <= i + 1
                    invariant
                        1 <= k,
                        k <= i + 2,
                        i + 1 <= 5,
                        f as nat == factorial((k - 1) as nat)
                    decreases (i + 2) - k
                {
                    proof {
                        factorial_bound_lemma((k - 1) as nat);
                        factorial_bound_lemma(k as nat);
                        assert(factorial(k as nat) == k as nat * factorial((k - 1) as nat));
                        assert(k <= 5);
                        assert(factorial((k - 1) as nat) <= 24);
                        assert(k as nat * factorial((k - 1) as nat) <= 120);
                    }
                    f = f * k;
                    k = k + 1;
                }
                assert(f as nat == factorial((i + 1) as nat));
                f
            } else {
                // For larger factorials, compute modulo 256
                while k <= i + 1
                    invariant
                        1 <= k,
                        k <= i + 2,
                        f as nat == factorial((k - 1) as nat) % 256
                    decreases (i + 2) - k
                {
                    let next_f = ((f as u16 * k as u16) % 256) as u8;
                    assert(next_f as nat == (f as nat * k as nat) % 256);
                    assert(next_f as nat == (factorial((k - 1) as nat) % 256 * k as nat) % 256);
                    assert(next_f as nat == (factorial((k - 1) as nat) * k as nat) % 256);
                    assert(next_f as nat == factorial(k as nat) % 256);
                    f = next_f;
                    k = k + 1;
                }
                assert(f as nat == factorial((i + 1) as nat) % 256);
                f
            }
        } else {
            // Sum case
            let mut s: u8 = 0;
            let mut k: u8 = 1;
            while k <= i + 1
                invariant
                    1 <= k,
                    k <= i + 2,
                    s as nat == sum_range((k - 1) as nat) % 256
                decreases (i + 2) - k
            {
                let next_s = ((s as u16 + k as u16) % 256) as u8;
                assert(next_s as nat == (s as nat + k as nat) % 256);
                assert(next_s as nat == (sum_range((k - 1) as nat) % 256 + k as nat) % 256);
                assert(next_s as nat == (sum_range((k - 1) as nat) + k as nat) % 256);
                assert(next_s as nat == sum_range(k as nat) % 256);
                s = next_s;
                k = k + 1;
            }
            assert(s as nat == sum_range((i + 1) as nat) % 256);
            s
        };
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}