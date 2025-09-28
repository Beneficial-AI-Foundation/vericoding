// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(n: int) -> bool {
    n >= 2 && (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): return spec predicate directly */
proof fn is_prime(n: usize) -> (result: bool)
    requires n < usize::MAX,
    ensures result <==> is_prime_number(n as int)
{
    let result = is_prime_number(n as int);
    result
}
// </vc-helpers>

// <vc-spec>
fn prime_length(s: Vec<char>) -> (result: bool)
    ensures result <==> is_prime_number(s@.len() as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute primality by trial division and add triggers for quantifiers */
    let n: usize = s.len();
    if n < 2 {
        let res: bool = false;
        proof {
            assert(res <==> is_prime_number(n as int));
        }
        return res;
    }
    let mut i: usize = 2;
    let mut found_div: bool = false;
    while i < n
        invariant
            2 <= i && i <= n,
            forall|k: usize| 2 <= k && k < i ==> #[trigger] (n % k) != 0,
        decreases n - i
    {
        if n % i == 0 {
            found_div = true;
            break;
        }
        i += 1;
    }
    let res: bool = !found_div;
    proof {
        if found_div {
            let k: int = i as int;
            assert(2 <= k && k < n as int);
            assert(((n as int) % k) == 0);
            assert(!is_prime_number(n as int));
            assert(!res);
        } else {
            assert(i == n);
            assert(forall|k: int| 2 <= k && k < n as int ==> #[trigger] ((n as int) % k) != 0);
            assert(is_prime_number(n as int));
            assert(res);
        }
        assert(res <==> is_prime_number(n as int));
    }
    res
}
// </vc-code>


}

fn main() {}