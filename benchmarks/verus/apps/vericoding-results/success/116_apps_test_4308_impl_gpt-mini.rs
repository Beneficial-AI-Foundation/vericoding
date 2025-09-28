// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 1 && n <= 100 && k <= 100
}

spec fn min_cracker_difference(n: int, k: int) -> int
    recommends k > 0
{
    if n % k == 0 { 0 } else { 1 }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate min_cracker_difference to remainder */
proof fn lemma_min_equiv(n: int, k: int)
    requires
        k > 0,
    ensures
        min_cracker_difference(n, k) == if n % k == 0 { 0int } else { 1int },
{
    // direct from the spec definition of min_cracker_difference
    assert(min_cracker_difference(n, k) == if n % k == 0 { 0int } else { 1int });
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == min_cracker_difference(n as int, k as int),
        result as int == 0 <==> (n as int) % (k as int) == 0,
        result as int == 1 <==> (n as int) % (k as int) != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute result using i8 operations and prove correspondence using ghost ints */
{
    let res: i8 = if (n % k) == 0 { 0i8 } else { 1i8 };
    proof {
        let ni: int = n as int;
        let ki: int = k as int;
        assert(ki > 0);
        lemma_min_equiv(ni, ki);
        if ni % ki == 0 {
            assert((res as int) == 0int);
            assert(min_cracker_difference(ni, ki) == 0int);
        } else {
            assert((res as int) == 1int);
            assert(min_cracker_difference(ni, ki) == 1int);
        }
        assert((res as int) == min_cracker_difference(ni, ki));
    }
    res
}

// </vc-code>


}

fn main() {}