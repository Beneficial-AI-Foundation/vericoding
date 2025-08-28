use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
spec fn prime(p: u32) -> (ret: bool) {
    spec_prime(p as int)
}

fn checked_mul_thrice(x: u32, y: u32, z: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> ret.unwrap() == x * y * z,
        ret.is_none() ==> x * y * z > u32::MAX,
{
    if (x == 0 || y == 0 || z == 0) {
        return Some(0);
    }
    assert(x > 0 && y > 0 && z > 0);
    let prod2 = x.checked_mul(y);
    if prod2.is_some() {
        let prod3 = prod2.unwrap().checked_mul(z);
        if prod3.is_some() {
            let ans = prod3.unwrap();
            assert(ans == x * y * z);
            Some(ans)
        } else {
            assert(x * y * z > u32::MAX);
            None
        }
    } else {
        broadcast use group_mul_properties;
        assert(x * y * z >= y * z);
        None
    }
}

fn is_prime_exec(p: u32) -> (ret: bool)
    ensures
        ret <==> spec_prime(p as int),
{
    if p <= 1 {
        return false;
    }
    for k in 2..p
        invariant
            forall|j: int| 1 < j < k ==> #[trigger] (p as int % j) != 0,
            k <= p,
    {
        if p % k == 0 {
            return false;
        }
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn is_multiply_prime(x: u32) -> (ans: bool)
    // pre-conditions-start
    requires
        x > 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ans <==> exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    for a in 2..x
        invariant
            forall|ap: int, bp: int, cp: int|
                spec_prime(ap) && spec_prime(bp) && spec_prime(cp) && 2 <= ap < a && x == ap * bp * cp ==> false,
            a <= x,
    {
        if !is_prime_exec(a) {
            continue;
        }
        if x % a != 0 {
            continue;
        }
        let rem = x / a;
        if rem < 1 {
            continue;
        }
        let loop_bound = if rem > u32::MAX - 1 { u32::MAX } else { rem + 1 };
        for b in 2..loop_bound
            invariant
                forall|bp: int, cp: int|
                    spec_prime(bp) && spec_prime(cp) && 2 <= bp < b && rem == bp * cp ==> false,
                b <= loop_bound,
                spec_prime(a as int),
                x % a == 0,
                rem == x / a,
                rem >= 1,
                loop_bound <= u32::MAX,
        {
            if b >= rem {
                continue;
            }
            if !is_prime_exec(b) {
                continue;
            }
            if rem % b != 0 {
                continue;
            }
            let c = rem / b;
            if c < 2 {
                continue;
            }
            if !is_prime_exec(c) {
                continue;
            }
            let triple_check = checked_mul_thrice(a, b, c);
            if triple_check.is_some() && triple_check.unwrap() == x {
                assert(spec_prime(a as int) && spec_prime(b as int) && spec_prime(c as int));
                assert(x == (a as int) * (b as int) * (c as int));
                return true;
            }
        }
    }
    false
}
// </vc-code>

}
fn main() {}