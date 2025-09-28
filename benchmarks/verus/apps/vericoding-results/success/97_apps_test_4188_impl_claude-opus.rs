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
    /* code modified by LLM (iteration 4): Fixed array indexing type errors */
    let truth_values: [i8; 16] = [1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0];
    
    proof {
        assert(truth_values[0] == 1);
        assert(truth_values[1] == 0);
        assert(truth_values[2] == 0);
        assert(truth_values[3] == 1);
        assert(truth_values[4] == 0);
        assert(truth_values[5] == 1);
        assert(truth_values[6] == 0);
        assert(truth_values[7] == 1);
        assert(truth_values[8] == 1);
        assert(truth_values[9] == 1);
        assert(truth_values[10] == 0);
        assert(truth_values[11] == 0);
        assert(truth_values[12] == 1);
        assert(truth_values[13] == 0);
        assert(truth_values[14] == 1);
        assert(truth_values[15] == 0);
        
        assert(fact_truth_values() =~= seq![1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0]);
        
        assert forall|i: int| 0 <= i < 16 implies truth_values[i] as int == fact_truth_values()[i] by {
            assert(truth_values[i] as int == fact_truth_values()[i]);
        }
    }
    
    let index = (n - 1) as usize;
    let result = truth_values[index];
    
    proof {
        assert(1 <= n <= 16);
        assert(0 <= index < 16);
        assert(result as int == truth_values[index as int] as int);
        assert(truth_values[index as int] as int == fact_truth_values()[index as int]);
        assert(index as int == n - 1);
        assert(fact_truth_values()[n - 1] == expected_output(n as int));
        assert(result as int == expected_output(n as int));
        assert(result == 0 || result == 1);
        assert(valid_output(result as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}