use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn sum_spec(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + sum_spec((n - 1) as nat) }
}

proof fn sum_formula(n: nat)
    ensures sum_spec(n) == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        assert(sum_spec(0) == 0);
        assert(0 * 1 / 2 == 0);
    } else {
        sum_formula((n - 1) as nat);
        assert(sum_spec(n) == n + sum_spec((n - 1) as nat));
        assert(sum_spec((n - 1) as nat) == (n - 1) * n / 2) by {
            assert((n - 1) * ((n - 1) + 1) / 2 == (n - 1) * n / 2);
        };
        assert(sum_spec(n) == n + (n - 1) * n / 2);
        assert(n + (n - 1) * n / 2 == (2 * n + (n - 1) * n) / 2) by {
            assert(n == 2 * n / 2);
        };
        assert((2 * n + (n - 1) * n) / 2 == (n * 2 + n * n - n) / 2) by {
            assert((n - 1) * n == n * (n - 1));
            assert(n * (n - 1) == n * n - n * 1);
            assert(n * n - n * 1 == n * n - n);
        };
        assert((n * 2 + n * n - n) / 2 == (n + n * n) / 2) by {
            assert(n * 2 - n == n * (2 - 1));
            assert(n * (2 - 1) == n * 1);
            assert(n * 1 == n);
        };
        assert((n + n * n) / 2 == n * (1 + n) / 2) by {
            assert(n + n * n == n * 1 + n * n);
            assert(n * 1 + n * n == n * (1 + n));
        };
        assert(n * (1 + n) / 2 == n * (n + 1) / 2);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut result: u32 = 0;
    let mut i: u32 = 1;
    
    while i <= n
        invariant 
            i <= n + 1,
            result == (i - 1) * i / 2,
            n <= 65535
        decreases n + 1 - i
    {
        proof {
            assert(i <= n);
            assert(n <= 65535);
            assert(i <= 65535);
            assert(result == (i - 1) * i / 2);
            assert((i - 1) * i / 2 <= i * i / 2);
            assert(i * i <= 65535 * 65535);
            assert(result <= u32::MAX - i);
        }
        result = result + i;
        i = i + 1;
        proof {
            assert(result == ((i - 1) - 1) * (i - 1) / 2 + (i - 1));
            assert(result == (i - 2) * (i - 1) / 2 + (i - 1));
            assert(result == ((i - 2) * (i - 1) + 2 * (i - 1)) / 2);
            assert(result == ((i - 2 + 2) * (i - 1)) / 2);
            assert(result == i * (i - 1) / 2);
        }
    }
    
    proof {
        sum_formula(n as nat);
        assert(i == n + 1);
        assert(result == n * (n + 1) / 2);
    }
    
    result
}
// </vc-code>

fn main() {}

}