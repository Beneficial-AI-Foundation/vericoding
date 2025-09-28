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
/* helper modified by LLM (iteration 4): relate one-step sum_prefix to vec_to_seq_int element */
proof fn sum_prefix_step(operations: Vec<i8>, i: nat)
    requires
        i < operations@.len(),
    ensures
        sum_prefix(vec_to_seq_int(operations), i + 1) == sum_prefix(vec_to_seq_int(operations), i) + vec_to_seq_int(operations)[i],
{
    assert(sum_prefix(vec_to_seq_int(operations), i + 1) == sum_prefix(vec_to_seq_int(operations), i) + vec_to_seq_int(operations)[i]);
}

// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 4): implement runtime scan using vec_to_seq_int and prove correspondence */
    let len: usize = operations.len();
    let mut i: usize = 0usize;
    let mut acc: i64 = 0i64;

    while i < len
        invariant
            0 <= i,
            i <= len,
            acc as int == sum_prefix(vec_to_seq_int(operations), i as nat),
            forall|k: nat| k <= i as nat ==> sum_prefix(vec_to_seq_int(operations), k) >= 0,
        decreases
            len - i
    {
        let ai: i64 = operations[i] as i64;
        let new_acc = acc + ai;
        let new_i = i + 1;
        if new_acc < 0 {
            proof {
                assert(acc as int == sum_prefix(vec_to_seq_int(operations), i as nat));
                sum_prefix_step(operations, i as nat);
                assert(sum_prefix(vec_to_seq_int(operations), new_i as nat) == acc as int + vec_to_seq_int(operations)[i as nat]);
                assert(vec_to_seq_int(operations)[i as nat] == ai as int);
                assert(sum_prefix(vec_to_seq_int(operations), new_i as nat) == new_acc as int);
                assert(new_acc < 0);
                assert(exists|k: int| k == new_i as int && 0 < k <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), k as nat) < 0);
            }
            return true;
        }
        acc = new_acc;
        i = new_i;
        proof {
            assert(acc as int == sum_prefix(vec_to_seq_int(operations), i as nat));
            assert(forall|k: nat| k <= i as nat ==> sum_prefix(vec_to_seq_int(operations), k) >= 0);
        }
    }

    proof {
        assert(i == len);
        assert(forall|k: int| 0 < k <= operations@.len() ==> #[trigger] sum_prefix(vec_to_seq_int(operations), k as nat) >= 0);
    }
    false
}

// </vc-code>


}

fn main() {}