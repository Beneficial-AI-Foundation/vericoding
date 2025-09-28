// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum_prefix(ops: Seq<int>, len: nat) -> int
  recommends len <= ops.len()
  decreases len
{
  if len == 0 { 0 }
  else { sum_prefix(ops, (len - 1) as nat) + ops[len - 1] }
}

spec fn vec_to_seq_int(v: Vec<i8>) -> Seq<int> {
  v@.map(|i, x: i8| x as int)
}

  // </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix compilation by using tracked ghost sum for int calculations and proper looping with invariants to check prefix sums */
    let mut sum: i32 = 0;
    let mut ghost_sum: int = 0;
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            i <= operations.len(),
            ghost_sum == sum_prefix(vec_to_seq_int(operations), i as nat),
            forall|j: nat| j < i ==> sum_prefix(vec_to_seq_int(operations), (j + 1) as nat) >= 0,
        decreases operations.len() - i
    {
        sum = sum + (operations[i] as i32);
        proof {
            ghost_sum = ghost_sum + (operations[i] as int);
        }
        if ghost_sum < 0 {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>


}

fn main() {}