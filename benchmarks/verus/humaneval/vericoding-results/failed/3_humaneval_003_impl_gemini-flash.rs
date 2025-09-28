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
/* helper modified by LLM (iteration 5): No changes to this section. Keeping previous iteration's corrections. */
proof fn lemma_sum_prefix_monotonic_increase(ops: Seq<int>, len: nat, i: nat)
    requires
        0 <= i,
        i <= len,
        len <= ops.len(),
        forall|j: nat| 0 <= j < len ==> ops[j] >= 0,
    ensures
        sum_prefix(ops, i) <= sum_prefix(ops, len),
    decreases len
{
    if i == len {
        // do nothing
    } else {
        lemma_sum_prefix_monotonic_increase(ops, (len - 1) as nat, i);
        assert(sum_prefix(ops, (len - 1) as nat) >= sum_prefix(ops, i));
        assert(ops[(len - 1) as nat] >= 0); // Corrected to use nat for indexing
        assert(sum_prefix(ops, len) == sum_prefix(ops, (len - 1) as nat) + ops[(len - 1) as nat]);
        assert(sum_prefix(ops, len) >= sum_prefix(ops, (len - 1) as nat));
        assert(sum_prefix(ops, len) >= sum_prefix(ops, i));
    }
}

/* helper modified by LLM (iteration 5): No changes to this section. Keeping previous iteration's corrections. */
proof fn lemma_sum_prefix_positive(ops: Seq<int>, len: nat)
    requires
        len <= ops.len(),
        forall|j: nat| 0 <= j < len ==> ops[j] >= 0,
    ensures
        sum_prefix(ops, len) >= 0,
    decreases len
{
    if len > 0 {
        lemma_sum_prefix_positive(ops, (len - 1) as nat);
        assert(sum_prefix(ops, (len - 1) as nat) >= 0);
        assert(ops[(len - 1) as nat] >= 0); // Corrected to use nat for indexing
        assert(sum_prefix(ops, len) == sum_prefix(ops, (len - 1) as nat) + ops[(len - 1) as nat]);
        assert(sum_prefix(ops, len) >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by changing `invariant style original` to a proper invariant block. */
{
    let ghost operations_seq = vec_to_seq_int(operations);
    let mut current_sum: i64 = 0;
    let mut i: usize = 0;

    while i < operations.len()
        invariant
            i <= operations.len(),
            current_sum as int == sum_prefix(operations_seq, i as nat),
    {
        if current_sum < 0 {
            return true;
        }

        let next_val: i8 = operations[i];
        current_sum = current_sum + next_val as i64;

        i = i + 1;
    }

    if current_sum < 0 {
        return true;
    }
    false
}
// </vc-code>


}

fn main() {}