// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1 <= n <= 16
}

spec fn fact_truth_values() -> Seq<int> {
    seq![1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]
}

spec fn valid_output(result: int) -> bool {
    result == 0 || result == 1
}

spec fn expected_output(n: int) -> int
    recommends valid_input(n)
{
    fact_truth_values()[n - 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reveal calls to proof bodies */
const FACT_TRUTH_VALUES: [i8; 16] = [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0];

proof fn truth_values_match_spec()
    ensures
        FACT_TRUTH_VALUES.view().len() == fact_truth_values().len(),
        forall|i: int| 0 <= i < fact_truth_values().len() ==> 
            FACT_TRUTH_VALUES.view()[i] as int == fact_truth_values()[i],
{
    reveal(fact_truth_values);
}

proof fn truth_values_are_valid()
    ensures
        forall|i: int| 0 <= i < fact_truth_values().len() ==>
            valid_output(fact_truth_values()[i]),
{
    reveal(fact_truth_values);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires 
        valid_input(n as int)
    ensures 
        valid_output(result as int),
        result as int == expected_output(n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): moved proof calls into a proof block */
    let result = FACT_TRUTH_VALUES[(n - 1) as usize];
    proof {
        truth_values_match_spec();
        truth_values_are_valid();
    }
    result
}
// </vc-code>


}

fn main() {}