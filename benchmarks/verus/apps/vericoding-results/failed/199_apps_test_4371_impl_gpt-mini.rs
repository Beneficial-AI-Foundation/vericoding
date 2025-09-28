// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() >= 3 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) >= '1' && #[trigger] s.index(i) <= '9'
}

spec fn string_to_int(s: Seq<char>) -> int {
    100 * ((s.index(0) as int) - ('0' as int)) + 
    10 * ((s.index(1) as int) - ('0' as int)) + 
    ((s.index(2) as int) - ('0' as int))
}

spec fn abs_diff(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn substring_at_index(s: Seq<char>, i: int) -> Seq<char> {
    s.subrange(i, i + 3)
}

spec fn is_minimum_difference(s: Seq<char>, result: int) -> bool {
    valid_input(s) ==> (
        result >= 0 &&
        (exists|i: int| 0 <= i <= s.len() - 3 && result == abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i)))) &&
        (forall|i: int| 0 <= i <= s.len() - 3 ==> result <= abs_diff(753 - string_to_int(#[trigger] substring_at_index(s, i))))
    )
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma relating substring to numeric value */
fn substring_value_agrees(s: Seq<char>, i: int)
    requires 0 <= i && i <= s.len() - 3,
    ensures string_to_int(substring_at_index(s, i)) == 100 * ((s.index(i) as int) - ('0' as int)) + 10 * ((s.index(i+1) as int) - ('0' as int)) + ((s.index(i+2) as int) - ('0' as int)),
{
    proof {
        assert(string_to_int(substring_at_index(s, i)) ==
            100 * ((substring_at_index(s, i).index(0) as int) - ('0' as int)) +
            10 * ((substring_at_index(s, i).index(1) as int) - ('0' as int)) +
            ((substring_at_index(s, i).index(2) as int) - ('0' as int))
        );
        assert(substring_at_index(s, i).index(0) == s.index(i));
        assert(substring_at_index(s, i).index(1) == s.index(i+1));
        assert(substring_at_index(s, i).index(2) == s.index(i+2));
        assert(100 * ((substring_at_index(s, i).index(0) as int) - ('0' as int)) +
               10 * ((substring_at_index(s, i).index(1) as int) - ('0' as int)) +
               ((substring_at_index(s, i).index(2) as int) - ('0' as int))
            ==
               100 * ((s.index(i) as int) - ('0' as int)) +
               10 * ((s.index(i+1) as int) - ('0' as int)) +
               ((s.index(i+2) as int) - ('0' as int))
        );
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires valid_input(s@)
    ensures is_minimum_difference(s@, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): move spec/lemma calls into proof blocks and use runtime i32/usize only */
    let n: usize = s.len();
    let mut best: i32 = 100 * ((s[0] as i32) - ('0' as i32)) + 10 * ((s[1] as i32) - ('0' as i32)) + ((s[2] as i32) - ('0' as i32));
    let mut best_diff: i32 = {
        let d: i32 = 753 - best;
        if d >= 0 { d } else { -d }
    };
    let mut i: usize = 1;

    proof {
        substring_value_agrees(s@, 0);
        assert(best as int == string_to_int(substring_at_index(s@, 0)));
        assert((best_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, 0))));
        assert(exists|j: int| 0 <= j && j <= (i as int) - 1 && (best_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, j))));
    }

    while i <= n - 3
        invariant
            1 <= (i as int) && (i as int) <= (n as int) - 2,
            exists|j: int| 0 <= j && j <= (i as int) - 1 && (best_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, j))),
            forall|j: int| 0 <= j && j <= (i as int) - 1 ==> (best_diff as int) <= abs_diff(753 - string_to_int(substring_at_index(s@, j))),
        decreases (n as int) - (i as int)
    {
        let old_i = i;
        let cur: i32 = 100 * ((s[old_i] as i32) - ('0' as i32)) + 10 * ((s[old_i + 1] as i32) - ('0' as i32)) + ((s[old_i + 2] as i32) - ('0' as i32));
        let diff: i32 = 753 - cur;
        let cur_diff: i32 = if diff >= 0 { diff } else { -diff };
        let old_best = best_diff;
        if cur_diff < old_best {
            best_diff = cur_diff;
        }
        i = old_i + 1;

        proof {
            substring_value_agrees(s@, old_i as int);
            assert(cur as int == string_to_int(substring_at_index(s@, old_i as int)));
            assert((cur_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, old_i as int))));
            if cur_diff < old_best {
                assert(best_diff == cur_diff);
                assert(best_diff as int == abs_diff(753 - string_to_int(substring_at_index(s@, (i as int) - 1))));
                assert(exists|j: int| 0 <= j && j <= (i as int) - 1 && (best_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, j))));
            } else {
                assert(best_diff == old_best);
                assert(exists|j: int| 0 <= j && j <= (old_i as int) - 1 && (old_best as int) == abs_diff(753 - string_to_int(substring_at_index(s@, j))));
                assert(exists|j: int| 0 <= j && j <= (i as int) - 1 && (best_diff as int) == abs_diff(753 - string_to_int(substring_at_index(s@, j))));
            }
            assert(forall|j: int| 0 <= j && j <= (i as int) - 1 ==> (best_diff as int) <= abs_diff(753 - string_to_int(substring_at_index(s@, j))));
        }
    }

    best_diff
}

// </vc-code>


}

fn main() {}