// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k > 0
}

spec fn is_correct_result(n: int, k: int, result: int) -> bool 
    recommends k > 0
{
    result > n && result % k == 0 && forall|x: int| n < x < result ==> #[trigger] (x % k) != 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mod_properties(a: int, k: int)
    requires
        k > 0,
    ensures
        forall|x: int|
            x >= a ==> (
            (x % k == 0) ==> (
                x >= a + (k - (a % k)) % k
            )),
{
    assert forall|x: int| x >= a implies (x % k == 0) implies x >= a + (k - (a % k)) % k by {
        assert((a % k) < k);
        assert((k - (a % k)) % k == if a % k == 0 {0} else {k - (a % k)});
    };
}

spec fn next_multiple(n: int, k: int) -> int
    recommends k > 0
{
    if n % k == 0 {
        n + k
    } else {
        n + (k - (n % k))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires valid_input(n as int, k as int)
    ensures is_correct_result(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed lemma assert syntax */
    let n_int = n as int;
    let k_int = k as int;
    
    if n_int % k_int == 0 {
        ((n_int + k_int) as i8)
    } else {
        ((n_int + (k_int - (n_int % k_int))) as i8)
    }
}
// </vc-code>


}

fn main() {}