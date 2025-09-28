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
proof fn lemma_sum_prefix_negative_exists(ops: Seq<int>, len: nat)
    requires
        len <= ops.len(),
        sum_prefix(ops, len) < 0,
    ensures
        exists|i: int| 0 < i <= len && #[trigger] sum_prefix(ops, i as nat) < 0,
    decreases len
{
    if len == 0 {
        assert(sum_prefix(ops, 0) == 0) by (compute);
        assert(false);
    } else {
        if sum_prefix(ops, (len - 1) as nat) < 0 {
            assert(exists|i: int| 0 < i <= len && sum_prefix(ops, i as nat) < 0);
        } else {
            assert(sum_prefix(ops, len) == sum_prefix(ops, (len - 1) as nat) + ops[len - 1]);
            assert(sum_prefix(ops, len) < 0);
            assert(ops[len - 1] < 0);
            assert(exists|i: int| i == len && #[trigger] sum_prefix(ops, i as nat) < 0);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix trigger annotation in proof */
    let mut sum: i8 = 0;
    let mut i: usize = 0;
    let n = operations.len();
    while i < n
        invariant
            i <= n,
            sum as int == sum_prefix(vec_to_seq_int(operations), i as nat),
            forall|j: int| 0 < j <= i ==> sum_prefix(vec_to_seq_int(operations), j as nat) >= 0,
        decreases n - i
    {
        let op = operations[i];
        sum = sum + op;
        if sum < 0 {
            proof {
                assert(i + 1 <= n);
                assert(0 < i + 1);
                assert(sum_prefix(vec_to_seq_int(operations), (i + 1) as nat) == sum as int);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        lemma_sum_prefix_negative_exists(vec_to_seq_int(operations), n as nat);
    }
    false
}
// </vc-code>


}

fn main() {}