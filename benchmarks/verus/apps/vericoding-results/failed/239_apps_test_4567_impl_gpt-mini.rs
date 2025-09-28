// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(scores: Seq<int>) -> bool {
    scores.len() > 0 && scores.len() <= 100 &&
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] >= 1 && #[trigger] scores[i] <= 100
}

spec fn sum_seq(scores: Seq<int>) -> int
    decreases scores.len()
{
    if scores.len() == 0 {
        0
    } else {
        scores[0] + sum_seq(scores.subrange(1, scores.len() as int))
    }
}

spec fn all_multiples_of_10(scores: Seq<int>) -> bool {
    forall|i: int| 0 <= i < scores.len() ==> #[trigger] scores[i] % 10 == 0
}

spec fn is_smallest_non_multiple(scores: Seq<int>, value: int) -> bool {
    scores.contains(value) && 
    value % 10 != 0 &&
    forall|x: int| #[trigger] scores.contains(x) && x % 10 != 0 ==> value <= x
}

spec fn correct_result(scores: Seq<int>, result: int) -> bool {
    let total_sum = sum_seq(scores);
    if total_sum % 10 != 0 {
        result == total_sum
    } else if all_multiples_of_10(scores) {
        result == 0
    } else {
        exists|smallest_non_multiple: int| 
            is_smallest_non_multiple(scores, smallest_non_multiple) &&
            result == total_sum - smallest_non_multiple
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min_int helper */
spec fn min_int(a: int, b: int) -> int {
    if a < b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn solve(scores: Vec<i8>) -> (result: i8)
    requires valid_input(scores@.map(|i, x| x as int))
    ensures correct_result(scores@.map(|i, x| x as int), result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime sum/min and relate to spec using invariants with explicit triggers */
    let mut total: i32 = 0;
    let mut min_non_multiple: i32 = 0;
    let mut found_non_multiple: bool = false;
    let mut all_mult: bool = true;
    let mut i: usize = 0;

    while i < scores.len()
        invariant
            0 <= i as int <= scores.len() as int,
            total as int == sum_seq((scores@).subrange(0, i as int).map(|j, y| y as int)),
            all_mult == (forall|k: int| 0 <= k < i as int ==> #[trigger] ((scores@).subrange(0, i as int).map(|j, y| y as int)@[k] % 10 == 0)),
            (!found_non_multiple) || (exists|k: int| 0 <= k < i as int && #[trigger] ((scores@).subrange(0, i as int).map(|j, y| y as int)@[k] == min_non_multiple as int) && (scores@).subrange(0, i as int).map(|j, y| y as int)@[k] % 10 != 0),
            (!found_non_multiple) || forall|k: int| 0 <= k < i as int ==> #[trigger] ((scores@).subrange(0, i as int).map(|j, y| y as int)@[k] % 10 != 0) ==> min_non_multiple as int <= (scores@).subrange(0, i as int).map(|j, y| y as int)@[k],
        decreases scores.len() as int - i as int
    {
        let v: i32 = scores[i] as i32;
        total = total + v;
        if v % 10 != 0 {
            all_mult = false;
            if !found_non_multiple {
                min_non_multiple = v;
                found_non_multiple = true;
            } else {
                if v < min_non_multiple {
                    min_non_multiple = v;
                }
            }
        }
        i = i + 1;
    }

    // compute result based on runtime values
    if total % 10 != 0 {
        let r: i8 = total as i8;
        proof {
            let seq = (scores@).map(|j, y| y as int);
            assert(total as int == sum_seq(seq.subrange(0, scores.len() as int)));
            assert(total as int % 10 != 0);
            assert(correct_result(seq, r as int));
        }
        r
    } else {
        if all_mult {
            let r: i8 = 0i8;
            proof {
                let seq = (scores@).map(|j, y| y as int);
                assert(total as int == sum_seq(seq.subrange(0, scores.len() as int)));
                assert(all_multiples_of_10(seq));
                assert(correct_result(seq, r as int));
            }
            r
        } else {
            proof {
                let seq = (scores@).map(|j, y| y as int);
                assert(total as int == sum_seq(seq.subrange(0, scores.len() as int)));
                assert(found_non_multiple);
                assert((min_non_multiple as int) % 10 != 0);
                assert(correct_result(seq, (total - min_non_multiple) as int));
            }
            let r: i8 = (total - min_non_multiple) as i8;
            r
        }
    }
}

// </vc-code>


}

fn main() {}