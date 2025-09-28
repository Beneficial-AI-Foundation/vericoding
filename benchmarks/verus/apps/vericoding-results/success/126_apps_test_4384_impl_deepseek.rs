// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 1998
}

spec fn expected_result(n: int) -> Seq<char> {
    if n < 1000 { seq!['A', 'B', 'C'] } else { seq!['A', 'B', 'D'] }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed proof function signatures */

proof fn lemma_valid_input_range(n: int)
    requires
        valid_input(n),
    ensures
        1 <= n <= 1998
{
}

proof fn lemma_small_n_implies_abc(n: int)
    requires
        valid_input(n),
        n < 1000,
    ensures
        expected_result(n) == seq!['A', 'B', 'C']
{
}

proof fn lemma_large_n_implies_abd(n: int)
    requires
        valid_input(n),
        n >= 1000,
    ensures
        expected_result(n) == seq!['A', 'B', 'D']
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i32) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures result@ == expected_result(n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Moved proof blocks and fixed return statements */
{
    proof {
        lemma_valid_input_range(n as int);
    }
    
    let result: Vec<char>;
    if n < 1000 {
        proof {
            lemma_small_n_implies_abc(n as int);
        }
        result = vec!['A', 'B', 'C'];
    } else {
        proof {
            lemma_large_n_implies_abd(n as int);
        }
        result = vec!['A', 'B', 'D'];
    }
    result
}
// </vc-code>


}

fn main() {}