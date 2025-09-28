// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(x: int) -> bool {
    x >= 1
}

spec fn triangular_number(n: int) -> int
    recommends n >= 0
{
    n * (n + 1) / 2
}

spec fn is_minimal_time(t: int, x: int) -> bool
    recommends x >= 1
{
    t >= 1 && 
    triangular_number(t) >= x &&
    (t == 1 || triangular_number(t - 1) < x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by using proof fn instead of lemma */

proof fn lemma_triangular_increasing(n: nat)
    ensures n >= 1 ==> triangular_number(n as int) >= triangular_number((n - 1) as int)
{
}

proof fn lemma_triangular_positive(n: nat)
    ensures n >= 1 ==> triangular_number(n as int) >= n as int
{
}

proof fn lemma_minimal_time_unique(t1: int, t2: int, x: int)
    requires is_minimal_time(t1, x), is_minimal_time(t2, x)
    ensures t1 == t2
{
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: i8)
    requires valid_input(x as int)
    ensures is_minimal_time(result as int, x as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved type casts to ghost variables to avoid exec code casting */
    let mut t: i8 = 1;
    
    while t < 127
        invariant
            t >= 1,
            t <= 127,
            triangular_number((t - 1) as int) < x as int
    {
        proof {
            lemma_triangular_increasing(t as nat);
            let ghost_t: int = t as int;
            let ghost_x: int = x as int;
            assert(triangular_number(ghost_t) >= triangular_number(ghost_t - 1));
        }
        
        proof {
            let ghost_t: int = t as int;
            let ghost_x: int = x as int;
            if triangular_number(ghost_t) >= ghost_x {
                assert(is_minimal_time(ghost_t, ghost_x));
                break;
            }
        }
        
        t = t + 1;
    }
    
    proof {
        lemma_triangular_positive(t as nat);
    }
    
    t
}
// </vc-code>


}

fn main() {}