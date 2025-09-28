// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn max_distributions(n: int) -> int
    recommends valid_input(n)
{
    if n % 3 == 0 { 2 * (n / 3) } else { 2 * (n / 3) + 1 }
}
// </vc-preamble>

// <vc-helpers>

proof fn lemma_max_distributions_property(n: int)
    requires
        valid_input(n),
    ensures
        max_distributions(n) >= 1,
        n % 3 == 0 ==> max_distributions(n) == 2 * (n / 3),
        n % 3 != 0 ==> max_distributions(n) == 2 * (n / 3) + 1
{
}

proof fn lemma_mod3_cases(n: int)
    ensures
        n % 3 == 0 || n % 3 == 1 || n % 3 == 2
{
    assert(n % 3 >= 0 && n % 3 < 3);
    if n % 3 == 0 {
    } else if n % 3 == 1 {
    } else {
        assert(n % 3 == 2);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        result >= 1,
        result as int == max_distributions(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): remove ghost code from executable, add proper conversion */
    let n_nat = n as u8;
    
    if n % 3 == 0 {
        ((n_nat / 3) * 2) as i8
    } else {
        ((n_nat / 3) * 2 + 1) as i8
    }
}
// </vc-code>


}

fn main() {}