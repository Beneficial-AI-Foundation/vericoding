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

proof fn lemma_fib_monotonic(i: nat, j: nat)
    // pre-conditions-start
    requires
        i <= j,
    // pre-conditions-end
    // post-conditions-start
    ensures
        spec_fib(i) <= spec_fib(j),
    decreases j - i,
    // post-conditions-end
{
    if i == j {
        // Base case: spec_fib(i) == spec_fib(j)
        return;
    }
    
    if i == 0 {
        // spec_fib(0) = 0, and spec_fib(j) >= 0 for any j
        return;
    }
    
    if i == 1 {
        if j == 1 {
            return;
        }
        // For j >= 2, we need to show spec_fib(1) <= spec_fib(j)
        // spec_fib(1) = 1
        if j == 2 {
            // spec_fib(2) = spec_fib(1) + spec_fib(0) = 1 + 0 = 1
            return;
        }
        // For j > 2, spec_fib(j) >= spec_fib(2) >= 1
        lemma_fib_monotonic(2, j);
        return;
    }
    
    // General case: i >= 2, j > i
    // We know spec_fib(i-1) <= spec_fib(j-1) and spec_fib(i-2) <= spec_fib(j-2)
    /* code modified by LLM (iteration 1): cast i-1, j-1, i-2, j-2 to nat for function calls */
    lemma_fib_monotonic((i-1) as nat, (j-1) as nat);
    lemma_fib_monotonic((i-2) as nat, (j-2) as nat);
    
    // spec_fib(i) = spec_fib(i-1) + spec_fib(i-2)
    // spec_fib(j) = spec_fib(j-1) + spec_fib(j-2)
    // Since spec_fib(i-1) <= spec_fib(j-1) and spec_fib(i-2) <= spec_fib(j-2)
    // We have spec_fib(i) <= spec_fib(j)
}
// pure-end

spec fn inner_expr_fib(n: u32, ret: Option<u32>) -> (result:bool) {
    match ret {
        None => spec_fib(n as nat) > u32::MAX,
        Some(f) => f == spec_fib(n as nat),
    }
}
// pure-end

fn fib(n: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        inner_expr_fib(n, ret),
    // post-conditions-end
{
    if n == 0 {
        return Some(0);
    } else if n == 1 {
        return Some(1);
    }
    
    let mut a: u32 = 0;
    let mut b: u32 = 1;
    let mut i: u32 = 2;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i <= n
        invariant
            2 <= i <= n + 1,
            a == spec_fib((i - 2) as nat),
            b == spec_fib((i - 1) as nat),
            spec_fib((i - 1) as nat) <= u32::MAX,
        decreases n - i,
    {
        // Check for overflow before computing
        if b > u32::MAX - a {
            return None;
        }
        
        let next = a + b;
        a = b;
        b = next;
        i = i + 1;
    }
    
    Some(b)
}

} // verus!
fn main() {}