use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}
// pure-end
// pure-end

spec fn brazilian_factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}
// pure-end

// <vc-helpers>
exec fn factorial_exec(i: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => factorial(i as nat) > u64::MAX,
            Some(f) => f == factorial(i as nat),
        },
{
    if i == 0 || i == 1 {
        return Some(1);
    }
    let mut f: u64 = 1;
    let mut j = 2;
    proof {
        assert(f == 1);
        assert(f == factorial(1 as nat));
    }
    while j <= i
        invariant
            2 <= j <= i + 1,
            f == factorial((j - 1) as nat),
        decreases i - j + 1
    {
        if f > u64::MAX / j {
            return None;
        }
        f *= j;
        proof {
            assert(f == (j as nat) * factorial((j - 1) as nat));
            assert(f == factorial(j as nat));
        }
        j += 1;
    }
    proof {
        assert(j == i + 1);
        assert(f == factorial(i as nat));
    }
    Some(f)
}
// </vc-helpers>

// <vc-spec>
fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    // post-conditions-start
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut bf: u64 = 1;
    let mut k: u64 = 1;
    while k <= n
        invariant
            1 <= k <= n + 1,
            bf == brazilian_factorial((k - 1) as nat),
        decreases n - k + 1
    {
        let f_opt = factorial_exec(k);
        match f_opt {
            None => return None,
            Some(f) => {
                if bf > u64::MAX / f {
                    return None;
                }
                bf *= f;
                proof {
                    assert(f == factorial(k as nat));
                    assert(bf == factorial(k as nat) * brazilian_factorial((k - 1) as nat));
                    assert(bf == brazilian_factorial(k as nat));
                }
            }
        }
        k += 1;
    }
    Some(bf)
}
// </vc-code>

} // verus!
fn main() {}