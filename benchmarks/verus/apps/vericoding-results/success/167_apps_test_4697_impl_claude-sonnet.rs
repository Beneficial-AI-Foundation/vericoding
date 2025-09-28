// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int) -> bool {
    n >= 0 && m >= 0
}

spec fn max_scc_groups(n: int, m: int) -> int {
    if valid_input(n, m) {
        let direct_groups = if n < m / 2 { n } else { m / 2 };
        let remaining_c_pieces = m - direct_groups * 2;
        let additional_groups = remaining_c_pieces / 4;
        direct_groups + additional_groups
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed exec functions to proof functions */
proof fn lemma_max_scc_groups_bounds(n: int, m: int)
    requires valid_input(n, m)
    ensures max_scc_groups(n, m) >= 0
{
}

proof fn lemma_max_scc_groups_computation(n: int, m: int)
    requires valid_input(n, m)
    ensures
        max_scc_groups(n, m) == {
            let direct_groups = if n < m / 2 { n } else { m / 2 };
            let remaining_c_pieces = m - direct_groups * 2;
            let additional_groups = remaining_c_pieces / 4;
            direct_groups + additional_groups
        }
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
  requires valid_input(n as int, m as int)
  ensures 
      result >= 0,
      result as int == max_scc_groups(n as int, m as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): moved lemma calls inside proof block */
    proof {
        lemma_max_scc_groups_bounds(n as int, m as int);
        lemma_max_scc_groups_computation(n as int, m as int);
    }
    
    let direct_groups = if n < m / 2 { n } else { m / 2 };
    let remaining_c_pieces = m - direct_groups * 2;
    let additional_groups = remaining_c_pieces / 4;
    let result = direct_groups + additional_groups;
    
    result
}
// </vc-code>


}

fn main() {}