use vstd::prelude::*;

verus! {

spec fn sum_ints(n: int) -> int
    decreases n when n >= 0
{
    if n <= 0 {
        0
    } else {
        sum_ints(n - 1) + n
    }
}

// <vc-helpers>
proof fn sum_ints_formula(n: int)
    requires n >= 0
    ensures sum_ints(n) == n * (n + 1) / 2
    decreases n
{
    if n == 0 {
        assert(sum_ints(0) == 0);
        assert(0 * (0 + 1) / 2 == 0);
    } else {
        sum_ints_formula(n - 1);
        assert(sum_ints(n - 1) == (n - 1) * n / 2);
        assert(sum_ints(n) == sum_ints(n - 1) + n);
        assert(sum_ints(n) == (n - 1) * n / 2 + n);
        assert((n - 1) * n / 2 + n == ((n - 1) * n + 2 * n) / 2);
        assert(((n - 1) * n + 2 * n) / 2 == (n * (n - 1) + 2 * n) / 2);
        assert((n * (n - 1) + 2 * n) / 2 == n * (n + 1) / 2);
    }
}

proof fn sum_ints_step(i: int)
    requires i >= 0
    ensures sum_ints(i + 1) == sum_ints(i) + (i + 1)
{
    assert(i + 1 > 0);
    assert(sum_ints(i + 1) == sum_ints((i + 1) - 1) + (i + 1));
    assert((i + 1) - 1 == i);
}
// </vc-helpers>

// <vc-spec>
fn sum_ints_loop(n: u32) -> (s: u32)
    ensures 
        s == sum_ints(n as int),
        s == n * (n + 1) / 2;
// </vc-spec>
// <vc-code>
{
    let mut s: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            s == sum_ints(i as int),
            s == (i as int) * ((i as int) + 1) / 2,
    {
        proof {
            sum_ints_formula(i as int);
            sum_ints_step(i as int);
        }
        
        i = i + 1;
        s = s + i;
        
        proof {
            assert(s == sum_ints((i - 1) as int) + (i as int));
            assert(sum_ints(i as int) == sum_ints((i - 1) as int) + (i as int));
            sum_ints_formula(i as int);
        }
    }
    
    proof {
        assert(i == n);
        sum_ints_formula(n as int);
    }
    
    s
}
// </vc-code>

fn main() {
}

}