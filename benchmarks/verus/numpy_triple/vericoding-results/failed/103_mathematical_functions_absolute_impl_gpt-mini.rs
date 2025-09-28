// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate abs_spec to i8 arithmetic */
proof fn abs_spec_eq_i8(x: i8)
    ensures
        abs_spec(x as int) == if x as int >= 0 { x as int } else { -(x as int) },
        abs_spec(x as int) >= 0,
        abs_spec(x as int) == 0 <==> x == 0,
{
    if x as int >= 0 {
        assert(abs_spec(x as int) == x as int);
        assert(abs_spec(x as int) >= 0);
        assert(abs_spec(x as int) == 0 <==> x == 0);
    } else {
        assert(abs_spec(x as int) == -(x as int));
        assert(abs_spec(x as int) >= 0);
        assert(abs_spec(x as int) == 0 <==> x == 0);
    }
}

// </vc-helpers>

// <vc-spec>
spec fn abs_spec(x: int) -> int {
    if x >= 0 { x } else { -x }
}

fn absolute(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == abs_spec(x[i] as int),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> x[i] == 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implement absolute using usize indices and Vec indexing without view */
{
    let mut result: Vec<i8> = Vec::new();
    let n: usize = x.len();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            forall|j: int| 0 <= j < (i as int) ==> result[j as usize] as int == abs_spec(x[j as usize] as int),
        decreases n - i
    {
        let xi: i8 = x[i];
        let ai: i8 = if xi >= 0 { xi } else { -xi };
        proof {
            abs_spec_eq_i8(xi);
            assert(ai as int == abs_spec(xi as int));
            assert(abs_spec(xi as int) >= 0);
            assert(abs_spec(xi as int) == 0 <==> xi == 0);
        }
        result.push(ai);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}