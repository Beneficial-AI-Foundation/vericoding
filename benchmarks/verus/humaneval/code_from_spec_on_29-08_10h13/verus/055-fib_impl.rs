use vstd::prelude::*;

verus! {

#[verifier::memoize]
spec fn spec_fib(n: nat) -> (ret:nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        1
    } else {
        spec_fib((n - 1) as nat) + spec_fib((n - 2) as nat)
    }
}
// pure-end
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_fib_monotonic(i: nat, j: nat)
    requires i <= j
    ensures spec_fib(i) <= spec_fib(j)
    decreases j
{
    if i == j {
        return;
    }
    if j == 0 {
        return;
    }
    if j == 1 {
        return;
    }
    lemma_fib_monotonic(i, (j-1) as nat);
    lemma_fib_monotonic((j-2) as nat, (j-1) as nat);
}

proof fn lemma_fib_grows(n: nat)
    requires n >= 5
    ensures spec_fib(n) >= n
    decreases n
{
    /* code modified by LLM (iteration 5): fixed precondition check and base cases */
    if n == 5 {
        assert(spec_fib(5) == spec_fib(4) + spec_fib(3));
        assert(spec_fib(4) == spec_fib(3) + spec_fib(2));
        assert(spec_fib(3) == spec_fib(2) + spec_fib(1));
        assert(spec_fib(2) == spec_fib(1) + spec_fib(0));
        assert(spec_fib(2) == 1 + 0);
        assert(spec_fib(3) == 1 + 1);
        assert(spec_fib(4) == 2 + 1);
        assert(spec_fib(5) == 3 + 2);
        assert(spec_fib(5) == 5);
        return;
    }
    if n == 6 {
        lemma_fib_grows(5);
        assert(spec_fib(6) == spec_fib(5) + spec_fib(4));
        assert(spec_fib(5) == 5);
        assert(spec_fib(4) == 3);
        assert(spec_fib(6) == 8);
        assert(spec_fib(6) >= 6);
        return;
    }
    lemma_fib_grows((n-1) as nat);
    lemma_fib_grows((n-2) as nat);
    assert(spec_fib(n) == spec_fib((n-1) as nat) + spec_fib((n-2) as nat));
    assert(spec_fib((n-1) as nat) >= (n-1) as nat);
    assert(spec_fib((n-2) as nat) >= (n-2) as nat);
    assert(spec_fib(n) >= (n-1) + (n-2));
    assert(spec_fib(n) >= n + n - 3);
    assert(n >= 5);
    assert(spec_fib(n) >= n);
}

proof fn lemma_fib_overflow_propagates(n: nat)
    requires n >= 2,
    requires spec_fib((n-1) as nat) > u32::MAX || spec_fib((n-2) as nat) > u32::MAX
    ensures spec_fib(n) > u32::MAX
{
    /* code modified by LLM (iteration 5): added lemma for overflow propagation */
    lemma_fib_monotonic((n-1) as nat, n);
    lemma_fib_monotonic((n-2) as nat, n);
    assert(spec_fib(n) == spec_fib((n-1) as nat) + spec_fib((n-2) as nat));
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def fib(n: int) -> int"
docstring: |
Return n-th Fibonacci number.
test_cases:
- input: 10
expected_output: 55
- input: 1
expected_output: 1
- input: 8
expected_output: 21
*/
// </vc-description>

// <vc-spec>
fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if n == 0 {
        return Some(0);
    }
    if n == 1 {
        return Some(1);
    }
    
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 2;
    
    /* code modified by LLM (iteration 5): enhanced overflow detection and postcondition satisfaction */
    while i <= n
        invariant
            2 <= i <= n + 1,
            a == spec_fib((i - 2) as nat),
            b == spec_fib((i - 1) as nat),
            spec_fib((i - 2) as nat) <= u32::MAX,
            spec_fib((i - 1) as nat) <= u32::MAX,
            i <= u32::MAX,
        decreases n + 1 - i,
    {
        proof {
            lemma_fib_monotonic((i - 2) as nat, (i - 1) as nat);
        }
        
        /* code modified by LLM (iteration 5): improved overflow check with postcondition proof */
        if a > u32::MAX - b {
            proof {
                assert(spec_fib(i as nat) == spec_fib((i-1) as nat) + spec_fib((i-2) as nat));
                assert(spec_fib(i as nat) == b + a);
                assert(spec_fib(i as nat) > u32::MAX);
                if i < n {
                    lemma_fib_overflow_propagates((i+1) as nat);
                    lemma_fib_monotonic(i as nat, n as nat);
                    assert(spec_fib(n as nat) > u32::MAX);
                } else {
                    assert(i == n);
                    assert(spec_fib(n as nat) > u32::MAX);
                }
            }
            return None;
        }
        
        let temp = a + b;
        proof {
            assert(temp == spec_fib(i as nat));
            assert(temp <= u32::MAX);
        }
        a = b;
        b = temp;
        
        if i == u32::MAX {
            proof {
                if i < n {
                    assert(spec_fib(n as nat) > u32::MAX);
                }
            }
            return None;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 5): added proof for successful completion */
    proof {
        assert(i == n + 1);
        assert(b == spec_fib(n as nat));
        assert(spec_fib(n as nat) <= u32::MAX);
    }
    Some(b)
}
// </vc-code>

} // verus!
fn main() {}