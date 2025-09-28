// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n
}

spec fn max_in_seq(s: Seq<int>) -> int
    recommends s.len() > 0
    decreases s.len()
    via max_in_seq_decreases
{
    if s.len() == 1 {
        s[0]
    } else {
        let tail = s.subrange(1, s.len() as int);
        let tail_max = max_in_seq(tail);
        if s[0] >= tail_max { s[0] } else { tail_max }
    }
}

#[via_fn]
proof fn max_in_seq_decreases(s: Seq<int>) {
    assume(false);
}

spec fn valid_result(n: int, heights: Seq<int>, result: int) -> bool
    recommends valid_input(n, heights)
{
    result == max_in_seq(heights) &&
    forall|i: int| 0 <= i < heights.len() ==> heights[i] <= result &&
    exists|i: int| 0 <= i < heights.len() && heights[i] == result
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma about max after appending element */
proof fn max_in_seq_append(s: Seq<int>, x: int)
    requires s.len() > 0,
    ensures max_in_seq(s + seq![x]) == if x > max_in_seq(s) { x } else { max_in_seq(s) },
    decreases s.len()
{
    if s.len() == 1 {
        let a = s[0];
        // s = [a], so max_in_seq(s) == a
        assert(max_in_seq(s) == a);
        // s + [x] has tail [x], whose max is x
        let t = s + seq![x];
        let tail = t.subrange(1, t.len() as int);
        assert(tail.len() == 1);
        assert(max_in_seq(tail) == x);
        if a >= x {
            // max is a
            assert(max_in_seq(t) == a);
            assert(if x > max_in_seq(s) { x } else { max_in_seq(s) } == a);
        } else {
            // max is x
            assert(max_in_seq(t) == x);
            assert(if x > max_in_seq(s) { x } else { max_in_seq(s) } == x);
        }
    } else {
        let tail_s = s.subrange(1, s.len() as int);
        // apply induction on tail
        max_in_seq_append(tail_s, x);
        let s0 = s[0];
        // relate max of s + [x] to s0 and max of tail_s + [x]
        let left_concat = s + seq![x];
        let tail_concat = tail_s + seq![x];
        // compute max_in_seq(s + [x]) by definition: compare s0 and max_in_seq(tail_concat)
        if s0 >= max_in_seq(tail_concat) {
            assert(max_in_seq(left_concat) == s0);
            // need to show RHS equals s0
            let rhs = if x > max_in_seq(s) { x } else { max_in_seq(s) };
            if max_in_seq(s) == s0 {
                assert(rhs == s0);
            } else {
                // max_in_seq(s) must be max_in_seq(tail_concat) in this case
                assert(rhs == max_in_seq(tail_concat));
                assert(s0 >= max_in_seq(tail_concat));
                // from above, left hand is s0
                assert(rhs == s0 || rhs == max_in_seq(tail_concat));
            }
        } else {
            // max is from tail_concat
            assert(max_in_seq(left_concat) == max_in_seq(tail_concat));
            let rhs = if x > max_in_seq(s) { x } else { max_in_seq(s) };
            // by induction rhs == max_in_seq(tail_concat) or equals max_in_seq(s)
            assert(rhs == max_in_seq(tail_concat) || rhs == max_in_seq(s));
            assert(max_in_seq(left_concat) == rhs);
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: i8)
    requires valid_input(n as int, heights@.map(|i, x: i8| x as int))
    ensures valid_result(n as int, heights@.map(|i, x: i8| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use tracked/ghost for Seq<int> and ints in proofs */
    let tracked seq: Seq<int> = heights@.map(|i, x: i8| x as int);
    // n > 0 by requires, so heights.len() > 0
    let mut i: usize = 1;
    let mut cur: i8 = heights.get(0);
    while i < heights.len()
        invariant
            0 <= i as int && i as int <= n as int,
            if i == 0 { true } else { cur as int == max_in_seq(seq.subrange(0, i as int)) },
        decreases heights.len() - i
    {
        let old_cur = cur;
        let v = heights.get(i);
        let ghost v_i: int = v as int;
        let ghost s: Seq<int> = seq.subrange(0, i as int);
        proof {
            max_in_seq_append(s, v_i);
        }
        if v_i > old_cur as int {
            cur = v;
            proof {
                assert(seq.subrange(0, (i as int) + 1) == s + seq![v_i]);
                max_in_seq_append(s, v_i);
                assert(cur as int == max_in_seq(seq.subrange(0, (i as int) + 1)));
            }
        } else {
            proof {
                assert(seq.subrange(0, (i as int) + 1) == s + seq![v_i]);
                max_in_seq_append(s, v_i);
                assert(old_cur as int == max_in_seq(s));
                assert(max_in_seq(seq.subrange(0, (i as int) + 1)) == if v_i > max_in_seq(s) { v_i } else { max_in_seq(s) });
                assert(old_cur as int == max_in_seq(seq.subrange(0, (i as int) + 1)));
                assert(cur as int == max_in_seq(seq.subrange(0, (i as int) + 1)));
            }
        }
        i = i + 1;
    }
    // loop finished: i == heights.len() == n
    cur
}

// </vc-code>


}

fn main() {}