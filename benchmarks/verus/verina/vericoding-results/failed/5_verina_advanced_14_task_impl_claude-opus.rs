// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_power_of_four_recursive(n: nat, m: nat) -> bool
    decreases n
{
    if m == 0 {
        n == 1
    } else if n == 0 {
        false
    } else if n % 4 == 0 {
        is_power_of_four_recursive(n / 4, m - 1)
    } else {
        false
    }
}

proof fn power_of_four_equiv(n: nat, m: nat)
    requires n == pow(4, m)
    ensures is_power_of_four_recursive(n, m)
    decreases m
{
    if m == 0 {
        assert(n == pow(4, 0) == 1);
    } else {
        assert(n == pow(4, m) == 4 * pow(4, (m - 1) as nat));
        assert(n % 4 == 0);
        assert(n / 4 == pow(4, (m - 1) as nat));
        power_of_four_equiv(n / 4, (m - 1) as nat);
    }
}

proof fn check_power_of_four(n: nat) -> (m: nat)
    requires n > 0
    requires n % 4 == 0 || n == 1
    ensures n == 1 ==> m == 0 && n == pow(4, m)
    ensures n > 1 && n % 4 == 0 && (n / 4) == pow(4, (m - 1) as nat) ==> n == pow(4, m)
    decreases n
{
    if n == 1 {
        assert(pow(4, 0) == 1);
        0
    } else if n % 4 == 0 {
        let sub_m = check_power_of_four(n / 4);
        assert(n / 4 == pow(4, sub_m));
        assert(n == 4 * (n / 4));
        assert(n == 4 * pow(4, sub_m));
        assert(n == pow(4, sub_m + 1));
        sub_m + 1
    } else {
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn if_power_of_four(n: nat) -> (result: bool)
    ensures result <==> (exists|m: nat| n == pow(4, m)),
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return false;
    }
    
    let mut current = n;
    let mut count: nat = 0;
    
    while current > 1
        invariant current > 0
        invariant n == current * pow(4, count)
        invariant (exists|m: nat| n == pow(4, m)) <==> (exists|k: nat| current == pow(4, k))
        decreases current
    {
        if current % 4 != 0 {
            assert(current > 1);
            assert(current % 4 != 0);
            proof {
                if exists|k: nat| current == pow(4, k) {
                    let k = choose|k: nat| current == pow(4, k);
                    if k == 0 {
                        assert(current == pow(4, 0) == 1);
                        assert(false);
                    } else {
                        assert(current == pow(4, k));
                        assert(pow(4, k) == 4 * pow(4, (k - 1) as nat));
                        assert(current % 4 == 0);
                        assert(false);
                    }
                }
            }
            return false;
        }
        current = current / 4;
        count = count + 1;
        
        proof {
            assert(n == (current * 4) * pow(4, (count - 1) as nat));
            assert(n == current * (4 * pow(4, (count - 1) as nat)));
            assert(4 * pow(4, (count - 1) as nat) == pow(4, count));
        }
    }
    
    assert(current == 1);
    proof {
        assert(n == 1 * pow(4, count));
        assert(n == pow(4, count));
    }
    
    true
}
// </vc-code>

}
fn main() {}