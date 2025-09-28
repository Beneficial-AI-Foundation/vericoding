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
/* code modified by LLM (iteration 5): use i64 for running sum to avoid ghost type conversion and maintain invariant with sum_prefix */
{
    let n = operations.len();
    let mut current_sum: i64 = 0;
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            current_sum as int == sum_prefix(vec_to_seq_int(operations), i as nat),
            (forall|j: int| 0 < j <= i ==> sum_prefix(vec_to_seq_int(operations), j as nat) >= 0),
        decreases n - i
    {
        let op_val = operations[i] as i64;
        current_sum += op_val;
        proof {
            assert(current_sum as int == sum_prefix(vec_to_seq_int(operations), (i+1) as nat));
        }
        if current_sum < 0 {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>


}

fn main() {}