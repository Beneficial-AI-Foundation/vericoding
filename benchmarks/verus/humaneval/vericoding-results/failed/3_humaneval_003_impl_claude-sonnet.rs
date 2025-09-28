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
/* helper modified by LLM (iteration 5): added decreases clause to recursive lemma */
proof fn lemma_sum_prefix_step(ops: Seq<int>, len: nat)
    requires len > 0, len <= ops.len()
    ensures sum_prefix(ops, len) == sum_prefix(ops, (len - 1) as nat) + ops[len - 1]
{
}

proof fn lemma_sum_prefix_monotonic(ops: Seq<int>, len1: nat, len2: nat)
    requires len1 <= len2, len2 <= ops.len()
    ensures sum_prefix(ops, len1) <= sum_prefix(ops, len2) || (exists|i: nat| len1 < i <= len2 && sum_prefix(ops, i) < sum_prefix(ops, len1))
    decreases len2 - len1
{
    if len1 < len2 {
        lemma_sum_prefix_monotonic(ops, len1, (len2 - 1) as nat);
        lemma_sum_prefix_step(ops, len2);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved vec_to_seq_int conversion to proof block */
    let mut sum = 0i32;
    
    for i in 0..operations.len()
        invariant
            sum == sum_prefix(vec_to_seq_int(operations), i as nat),
            forall|j: int| 0 < j <= i ==> sum_prefix(vec_to_seq_int(operations), j as nat) >= 0
    {
        sum = sum + operations[i] as i32;
        
        proof {
            let ops_seq = vec_to_seq_int(operations);
            lemma_sum_prefix_step(ops_seq, (i + 1) as nat);
        }
        
        if sum < 0 {
            return true;
        }
    }
    
    false
}
// </vc-code>


}

fn main() {}