use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_spec_fibfib_bounds(n: nat)
    ensures n <= 30 ==> spec_fibfib(n) <= 0x7fffffff
    decreases n
{
    if n <= 30 {
        if n <= 2 {
        } else {
            lemma_spec_fibfib_bounds((n - 1) as nat);
            lemma_spec_fibfib_bounds((n - 2) as nat);
            lemma_spec_fibfib_bounds((n - 3) as nat);
        }
    }
}

proof fn lemma_spec_fibfib_monotonic(n: nat)
    ensures n >= 3 ==> spec_fibfib(n) >= spec_fibfib((n - 1) as nat)
    decreases n
{
    if n >= 3 {
        if n == 3 {
        } else {
            lemma_spec_fibfib_monotonic((n - 1) as nat);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)
    // post-conditions-start
    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if x <= 30 {
        proof {
            lemma_spec_fibfib_bounds(x as nat);
        }
        
        if x == 0 {
            Some(0)
        } else if x == 1 {
            Some(0)
        } else if x == 2 {
            Some(1)
        } else {
            let a = fibfib(x - 1)?;
            let b = fibfib(x - 2)?;
            let c = fibfib(x - 3)?;
            
            let sum1 = a.checked_add(b)?;
            let result = sum1.checked_add(c)?;
            
            Some(result)
        }
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}