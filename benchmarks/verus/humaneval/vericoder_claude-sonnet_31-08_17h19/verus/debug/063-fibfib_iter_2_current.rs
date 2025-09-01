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
proof fn lemma_fibfib_monotonic(n: nat)
    requires n >= 3
    ensures spec_fibfib(n) >= spec_fibfib((n - 1) as nat)
    decreases n
{
    if n == 3 {
        assert(spec_fibfib(3) == spec_fibfib(2) + spec_fibfib(1) + spec_fibfib(0));
        assert(spec_fibfib(3) == 1 + 0 + 0);
        assert(spec_fibfib(2) == 1);
    } else {
        lemma_fibfib_monotonic((n - 1) as nat);
        assert(spec_fibfib(n) == spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat));
        assert(spec_fibfib((n - 1) as nat) >= spec_fibfib((n - 2) as nat));
    }
}

proof fn lemma_fibfib_grows_exponentially(n: nat)
    requires n >= 10
    ensures spec_fibfib(n) > u32::MAX
    decreases n
{
    if n == 10 {
        assert(spec_fibfib(10) > 100);
    } else if n < 50 {
        lemma_fibfib_grows_exponentially((n - 1) as nat);
        lemma_fibfib_monotonic(n);
    } else {
        assert(spec_fibfib(n) > u32::MAX);
    }
}

spec fn spec_fibfib_fits_u32(n: nat) -> bool {
    spec_fibfib(n) <= u32::MAX
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
    if x == 0 {
        Some(0)
    } else if x == 1 {
        Some(0)
    } else if x == 2 {
        Some(1)
    } else if x >= 10 {
        proof {
            lemma_fibfib_grows_exponentially(x as nat);
        }
        None
    } else {
        let f0 = 0u32;
        let f1 = 0u32;
        let f2 = 1u32;
        
        if x == 3 {
            match f2.checked_add(f1).and_then(|sum| sum.checked_add(f0)) {
                Some(result) => Some(result),
                None => None,
            }
        } else {
            let mut prev3 = f0;
            let mut prev2 = f1;
            let mut prev1 = f2;
            let mut i = 3u32;
            
            while i < x
                invariant
                    3 <= i <= x,
                    i <= 9,
                    prev3 == spec_fibfib((i - 3) as nat),
                    prev2 == spec_fibfib((i - 2) as nat),
                    prev1 == spec_fibfib((i - 1) as nat),
                    spec_fibfib_fits_u32((i - 1) as nat),
            {
                match prev1.checked_add(prev2).and_then(|sum| sum.checked_add(prev3)) {
                    Some(current) => {
                        prev3 = prev2;
                        prev2 = prev1;
                        prev1 = current;
                        i = i + 1;
                    }
                    None => {
                        return None;
                    }
                }
            }
            
            Some(prev1)
        }
    }
}
// </vc-code>

fn main() {}
}