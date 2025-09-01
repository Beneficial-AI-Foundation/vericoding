use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}

fn is_prime(n: int) -> (ret: bool)
    requires
        n > 1,
    ensures
        ret <==> spec_prime(n),
{
    let mut i: int = 2;
    while i < n {
        invariant 2 <= i <= n;
        decreases (n - i) as nat;
        if n % i == 0 {
            return false;
        }
        i += 1;
    }
    true
}

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
    verus! {
        // implementation of is_multiply_prime
        let xi: int = x as int;
        let mut a: int = 2;
        while a <= xi {
            invariant 2 <= a <= xi + 1;
            decreases (xi - a) as nat;
            if xi % a == 0 {
                let rem_ab: int = xi / a;
                let mut b: int = 2;
                while b <= rem_ab {
                    invariant 2 <= b <= rem_ab + 1;
                    decreases (rem_ab - b) as nat;
                    if rem_ab % b == 0 {
                        let c: int = rem_ab / b;
                        if c >= 2 {
                            let pa = is_prime(a);
                            let pb = is_prime(b);
                            let pc = is_prime(c);
                            if pa && pb && pc {
                                proof {
                                    // From is_prime ensures, pa/pb/pc imply spec_prime for a,b,c
                                    assert(spec_prime(a));
                                    assert(spec_prime(b));
                                    assert(spec_prime(c));
                                    // Provide existential witness for the post-condition
                                    assert(exists |aa: int, bb: int, cc: int|
                                        aa == a && bb == b && cc == c &&
                                        spec_prime(aa) && spec_prime(bb) && spec_prime(cc) &&
                                        xi == aa * bb * cc);
                                }
                                return true;
                            }
                        }
                    }
                    b += 1;
                }
            }
            a += 1;
        }
        false
    }
}
// </vc-code>

fn main() {}
}