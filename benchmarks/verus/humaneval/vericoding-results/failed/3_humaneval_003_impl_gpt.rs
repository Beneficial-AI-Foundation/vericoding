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
/* helper modified by LLM (iteration 3): step lemma for sum_prefix */
proof fn lemma_sum_prefix_step(ops: Seq<int>, i: nat)
    ensures
        i < ops.len() ==> sum_prefix(ops, i + 1) == sum_prefix(ops, i) + ops[i],
{
    if i < ops.len() {
        assert(sum_prefix(ops, i + 1) == sum_prefix(ops, i) + ops[i]);
    }
}

/* helper modified by LLM (iteration 3): relate vec_to_seq_int indexing with original vector */
proof fn lemma_vec_to_seq_index(v: Vec<i8>, i: nat)
    ensures
        i < v@.len() ==> vec_to_seq_int(v)[i] == v@[i] as int,
{
    if i < v@.len() {
        let s = vec_to_seq_int(v);
        assert(s[i] == v@[i] as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn below_zero(operations: Vec<i8>) -> (result: bool)
  ensures result <==> (exists|i: int| 0 < i <= operations@.len() && #[trigger] sum_prefix(vec_to_seq_int(operations), i as nat) < 0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement scan with invariants; fix casts and indexing; connect runtime and spec sums */
    let s = vec_to_seq_int(operations);

    let mut i: usize = 0;
    let mut result: bool = false;
    let mut witness: usize = 0;
    let mut running: i128 = 0;

    while i < operations.len()
        invariant
            i <= operations.len(),
            s.len() == operations@.len(),
            result ==> (0 < witness && witness <= i && sum_prefix(s, (witness as nat)) < 0),
            !result ==> (sum_prefix(s, (i as nat)) == running as int && forall|j: nat| j <= (i as nat) ==> sum_prefix(s, j) >= 0),
        decreases operations.len() - i
    {
        let x_i128 = operations[i] as i128;
        if !result {
            let prev_running = running;
            let new_running = prev_running + x_i128;

            proof {
                assert(i < operations.len());
                assert((i as nat) < operations@.len());
                assert(s.len() == operations@.len());
                assert((i as nat) < s.len());
                lemma_sum_prefix_step(s, i as nat);
                lemma_vec_to_seq_index(operations, i as nat);
                assert(s[(i as nat)] == operations@[(i as nat)] as int);
                assert(operations@[(i as nat)] == operations[i]);
            }

            if new_running < 0 {
                result = true;
                witness = i + 1;
                running = new_running;
                proof {
                    assert(sum_prefix(s, ((i + 1) as nat)) == sum_prefix(s, (i as nat)) + s[(i as nat)]);
                    assert(sum_prefix(s, (i as nat)) == prev_running as int);
                    assert(new_running as int == prev_running as int + x_i128 as int);
                    assert(x_i128 as int == operations[i] as int);
                    assert(operations@[(i as nat)] == operations[i]);
                    assert(s[(i as nat)] == operations@[(i as nat)] as int);
                    assert(new_running as int == prev_running as int + s[(i as nat)]);
                    assert(sum_prefix(s, ((i + 1) as nat)) == new_running as int);
                    assert(sum_prefix(s, ((i + 1) as nat)) < 0);
                }
            } else {
                running = new_running;
                proof {
                    assert(sum_prefix(s, ((i + 1) as nat)) == sum_prefix(s, (i as nat)) + s[(i as nat)]);
                    assert(sum_prefix(s, (i as nat)) == prev_running as int);
                    assert(new_running as int == prev_running as int + x_i128 as int);
                    assert(x_i128 as int == operations[i] as int);
                    assert(operations@[(i as nat)] == operations[i]);
                    assert(s[(i as nat)] == operations@[(i as nat)] as int);
                    assert(new_running as int == prev_running as int + s[(i as nat)]);
                    assert(sum_prefix(s, ((i + 1) as nat)) == new_running as int);
                    assert(sum_prefix(s, ((i + 1) as nat)) >= 0);
                }
            }
        }
        i += 1;
    }

    proof {
        assert(i >= operations.len());
        assert(i <= operations.len());
        assert(i == operations.len());
        assert(s.len() == operations@.len());
        assert((i as nat) == s.len());

        if result {
            assert(0 < witness && witness <= i);
            assert((witness as nat) <= s.len());
            assert(sum_prefix(s, (witness as nat)) < 0);
            assert(exists|k: int| k == witness as int && 0 < k && k <= s.len() && sum_prefix(s, (k as nat)) < 0);
        } else {
            assert(forall|j: nat| j <= s.len() ==> sum_prefix(s, j) >= 0);
            assert(!(exists|k: int| 0 < k && k <= s.len() && sum_prefix(s, (k as nat)) < 0));
        }
    }

    result
}
// </vc-code>


}

fn main() {}