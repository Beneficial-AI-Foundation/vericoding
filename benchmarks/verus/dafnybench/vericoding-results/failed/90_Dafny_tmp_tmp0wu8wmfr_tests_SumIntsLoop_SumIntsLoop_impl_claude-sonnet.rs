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
    if n <= 0 {
        assert(sum_ints(n) == 0);
        assert(n * (n + 1) / 2 == 0);
    } else {
        sum_ints_formula(n - 1);
        assert(sum_ints(n - 1) == (n - 1) * n / 2);
        assert(sum_ints(n) == sum_ints(n - 1) + n);
        assert(sum_ints(n) == (n - 1) * n / 2 + n);
        assert(sum_ints(n) == (n - 1) * n / 2 + 2 * n / 2);
        assert(sum_ints(n) == ((n - 1) * n + 2 * n) / 2);
        assert(sum_ints(n) == (n * n - n + 2 * n) / 2);
        assert(sum_ints(n) == (n * n + n) / 2);
        assert(sum_ints(n) == n * (n + 1) / 2);
    }
}

proof fn sum_ints_iterative(k: int, n: int)
    requires 0 <= k <= n
    ensures sum_ints(n) == sum_ints(k) + sum_ints_range(k + 1, n)
    decreases n - k
{
    if k == n {
        assert(sum_ints(k) == sum_ints(n));
        assert(sum_ints_range(k + 1, n) == 0);
    } else {
        sum_ints_iterative(k + 1, n);
        assert(sum_ints(k) == sum_ints(k - 1) + k) by {
            if k > 0 {
                assert(sum_ints(k) == sum_ints(k - 1) + k);
            }
        }
    }
}

spec fn sum_ints_range(start: int, end: int) -> int
    decreases end - start when start <= end
{
    if start > end {
        0
    } else {
        sum_ints_range(start + 1, end) + start
    }
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
    proof {
        sum_ints_formula(n as int);
    }
    
    let mut i: u32 = 0;
    let mut s: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            s == sum_ints(i as int),
    {
        i = i + 1;
        s = s + i;
        
        proof {
            assert(sum_ints(i as int) == sum_ints((i - 1) as int) + i as int);
        }
    }
    
    proof {
        assert(i == n);
        assert(s == sum_ints(n as int));
        sum_ints_formula(n as int);
        assert(s == n * (n + 1) / 2);
    }
    
    s
}
// </vc-code>

fn main() {
}

}