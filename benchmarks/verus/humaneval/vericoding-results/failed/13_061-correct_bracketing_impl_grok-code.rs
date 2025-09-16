// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (ret:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '(' => (x + 1, b),
                    ')' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added recursive helper function for prefix correctness to enable verification of loop invariant. */
spec fn spec_bracketing_helper_prefix(brackets: Seq<char>, end: int) -> (int, bool)
    requires
        0 <= end <= brackets.len(),
    decreases end
{
    if end == 0 {
        (0, true)
    } else {
        let (x, b) = spec_bracketing_helper_prefix(brackets, end - 1);
        let c = brackets.index(end - 1);
        match c {
            '(' => (x + 1, b),
            ')' => (x - 1, b && x - 1 >= 0),
            _ => (x, b),
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)

    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,

    ensures
        ret <==> spec_bracketing(brackets@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed compilation error by using commas in invariant block and corrected invariant range to 0 <= i <= len. */
    let len = brackets@.len();
    let mut count: i32 = 0;
    let mut valid: bool = true;
    let mut i: int = 0;
    while i < len
        invariant
            0 <= i <= len,
            0 <= count,
            spec_bracketing_helper_prefix(brackets@, i) == (count as int, valid),
        decreases len - i
    {
        let c = brackets@[i];
        match c {
            '(' => {
                count += 1;
            },
            ')' => {
                if count > 0 {
                    count -= 1;
                } else {
                    valid = false;
                }
            },
            _ => {}
        }
        i = i + 1;
    }
    let result = valid && count == 0;
    proof {
        assert(spec_bracketing_helper_prefix(brackets@, brackets@.len()) == spec_bracketing_helper(brackets@));
        assert(spec_bracketing(brackets@) == result);
    }
    result
}
// </vc-code>

}
fn main() {}