// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed seq! macro syntax, use ghost variables, and proper type handling */
#[verifier::spec]
fn cum_sum_helper(a: Seq<i8>, i: nat) -> int
    decreases i
    requires i <= a.len(),
    ensures result == a.subrange(0, i as int).sum()
{
    if i == 0 {
        0
    } else {
        cum_sum_helper(a, i - 1) + a[i - 1] as int
    }
}
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed int/nat usage, ghost variables, and sequence operations */
{
    let n = a.len();
    let mut result = Vec::<i8>::new();
    
    proof {
        let a_seq = a@;
        let mut i: nat = 0;
        while i < n
            invariant
                i <= n,
                result@ = a_seq.subrange(0, i as int).mapi(|k: int| (a_seq[k] as int) as i8)
        {
            result.push((a_seq.subrange(0, (i + 1) as int).sum() as i8));
            i = i + 1;
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}