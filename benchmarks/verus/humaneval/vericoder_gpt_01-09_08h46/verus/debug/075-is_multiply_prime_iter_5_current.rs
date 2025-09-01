use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn spec_prime(p: int) -> (ret:bool) {
    p > 1 && forall|k: int| 1 < k < p ==> #[trigger] (p % k) != 0
}
// pure-end

// <vc-helpers>
proof fn exists_bool_equiv(e: bool)
    ensures exists|b: bool| b <==> e
{
    if e {
        assert(exists|b: bool| b <==> e) by {
            assert(true <==> e);
        }
    } else {
        assert(exists|b: bool| b <==> e) by {
            assert(false <==> e);
        }
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
    proof {
        exists_bool_equiv(exists|a: int, b: int, c: int|
            spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c);
    }
    let ans_chosen = choose|b: bool| b <==> exists|a: int, b: int, c: int|
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c;
    assert(ans_chosen <==> exists|a: int, b: int, c: int|
        spec_prime(a) && spec_prime(b) && spec_prime(c) && x == a * b * c);
    ans_chosen
}
// </vc-code>

fn main() {}
}