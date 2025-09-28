// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): exec primality check with triggers and proper decreases */
fn is_prime(n: usize) -> (result: bool)
    ensures
        result <==> is_prime_number(n as int),
{
    if n < 2 {
        proof {
            assert(!is_prime_number(n as int));
        }
        return false;
    }
    let ghost nn: int = n as int;
    let mut i: usize = 2;
    let mut ok: bool = true;
    while i < n
        invariant
            2 <= i as int,
            i as int <= nn,
            ok ==> (forall|k: int| 2 <= k && k < i as int ==> #[trigger] (nn % k) != 0),
            !ok ==> exists|k: int| 2 <= k && k < i as int && nn % k == 0,
        decreases nn - i as int
    {
        if n % i == 0 {
            proof {
                assert(2 <= i as int);
                assert(i > 0);
                assert(((n as int) % (i as int)) == ((n % i) as int));
                assert(nn % (i as int) == 0);
            }
            ok = false;
        } else {
            proof {
                assert(2 <= i as int);
                assert(i > 0);
                assert(((n as int) % (i as int)) == ((n % i) as int));
                assert(nn % (i as int) != 0);
            }
        }
        i = i + 1;
    }
    proof {
        assert(i as int == nn);
        assert(nn >= 2);
        if ok {
            assert(forall|k: int| 2 <= k && k < nn ==> #[trigger] (nn % k) != 0);
            assert(is_prime_number(nn));
        } else {
            assert(exists|k: int| 2 <= k && k < nn && nn % k == 0);
            assert(!is_prime_number(nn));
        }
    }
    ok
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): call is_prime and relate vector length to spec */
    let n = s.len();
    let result = is_prime(n);
    proof {
        assert(n as int == s@.len() as int);
    }
    result
}
// </vc-code>


}

fn main() {}