// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn max_height_up_to(heights: Seq<int>, index: int) -> int
    decreases index + 1
{
    if heights.len() > 0 && -1 <= index < heights.len() {
        if index < 0 {
            0
        } else if index == 0 {
            heights[0]
        } else if heights[index] > max_height_up_to(heights, index - 1) {
            heights[index]
        } else {
            max_height_up_to(heights, index - 1)
        }
    } else {
        0
    }
}

spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n >= 1 && heights.len() == n && (forall|i: int| 0 <= i < heights.len() ==> heights[i] >= 1)
}

spec fn can_make_non_decreasing(heights: Seq<int>) -> bool {
    if heights.len() > 0 {
        forall|i: int| 0 <= i < heights.len() ==> heights[i] >= max_height_up_to(heights, i) - 1
    } else {
        true
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced invalid `lemma` with a proper function lemma and used reveal(...) */
fn max_height_up_to_cons(heights: Seq<int>, i: int)
    requires heights.len() > 0 && -1 <= i < heights.len(),
    ensures max_height_up_to(heights, i) == if heights[i] > max_height_up_to(heights, i - 1) then heights[i] else max_height_up_to(heights, i - 1),
{
    proof {
        reveal(max_height_up_to);
        if heights[i] > max_height_up_to(heights, i - 1) {
            assert(max_height_up_to(heights, i) == heights[i]);
        } else {
            assert(max_height_up_to(heights, i) == max_height_up_to(heights, i - 1));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: String)
    requires valid_input(n as int, heights@.map(|i: int, v: i8| v as int))
    ensures (result@ == seq!['Y', 'e', 's']) <==> can_make_non_decreasing(heights@.map(|i: int, v: i8| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): loop with invariants and proof relating runtime max to spec max */
    let seq = heights@.map(|i: int, v: i8| v as int);
    let mut i: int = 0;
    let n_int: int = n as int;
    let mut cur_max: int = 0;
    let mut ok: bool = true;

    while i < n_int
        invariant
            0 <= i <= n_int,
            cur_max == max_height_up_to(seq, i - 1),
            ok == (forall|j: int| 0 <= j < i ==> seq[j] >= max_height_up_to(seq, j) - 1),
        decreases n_int - i
    {
        let idx = i;
        let h: int = heights[idx as nat] as int;
        let new_max: int = if h > cur_max { h } else { cur_max };
        let cond: bool = h >= new_max - 1;
        let new_ok: bool = ok && cond;

        proof {
            // relate runtime value h to spec sequence value
            assert(h == seq[idx]);
            // invariant gives cur_max == max_height_up_to(seq, idx - 1)
            assert(cur_max == max_height_up_to(seq, idx - 1));
            // apply lemma to get characterization of max_height_up_to at idx
            max_height_up_to_cons(seq, idx);
            // case analysis to relate new_max and spec max
            if h > cur_max {
                assert(new_max == h);
                assert(max_height_up_to(seq, idx) == h);
            } else {
                assert(new_max == cur_max);
                assert(max_height_up_to(seq, idx) == cur_max);
            }
            assert(new_max == max_height_up_to(seq, idx));
            // cond corresponds to the spec condition at idx
            assert(cond == (seq[idx] >= max_height_up_to(seq, idx) - 1));
            // new_ok is the forall property extended by one element
            assert(new_ok == (forall|j: int| 0 <= j < idx + 1 ==> seq[j] >= max_height_up_to(seq, j) - 1));
        }

        i = idx + 1;
        cur_max = new_max;
        ok = new_ok;
    }

    if ok { String::from("Yes") } else { String::from("No") }
}
// </vc-code>


}

fn main() {}