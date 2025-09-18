// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
{/* helper modified by LLM (iteration 5): proves count_true(s) <= s.len() */
proof fn count_true_le_len(s: Seq<bool>) ensures count_true(s) <= s.len() decreases s.len() {
    if s.len() == 0 {
    } else {
        let tail = s.skip(1);
        count_true_le_len(tail);
        assert(count_true(tail) <= tail.len());
        if s[0] {
            assert(count_true(s) == 1 + count_true(tail));
            assert(1 + count_true(tail) <= 1 + tail.len());
            assert(1 + tail.len() == s.len());
            assert(count_true(s) <= s.len());
        } else {
            assert(count_true(s) == count_true(tail));
            assert(count_true(tail) <= tail.len());
            assert(count_true(s) <= s.len());
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): copy the first k entries of arr into result (k = count_true(condition@)), using nat indices */
    let k: nat = count_true(condition@) as nat;
    let n: nat = arr.len();

    proof {
        count_true_le_len(condition@);
    }
    assert(k <= n);

    let mut result: Vec<f32> = Vec::<f32>::new();
    let mut i: nat = 0;
    while i < k
        invariant i <= k;
        invariant result.len() == i;
        invariant forall |j: nat| j < i ==> result@[j] == arr@[j];
        decreases k - i;
    {
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}