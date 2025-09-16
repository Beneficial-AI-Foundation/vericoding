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
/* helper modified by LLM (iteration 5): prefix-based spec computing bracket count and validity */
spec fn spec_bracketing_prefix(brackets: Seq<char>, i: nat) -> (int, bool) {
    if i == 0 {
        (0, true)
    } else {
        let (x, b) = spec_bracketing_prefix(brackets, i - 1);
        match brackets@.index(i - 1) {
            '(' => (x + 1, b),
            ')' => (x - 1, b && x - 1 >= 0),
            _ => (x, b),
        }
    }
}

/* helper modified by LLM (iteration 5): proof that the fold_left spec equals the prefix spec */
proof fn spec_bracketing_helper_prefix_equiv(brackets: Seq<char>)
    ensures
        spec_bracketing_helper(brackets) == spec_bracketing_prefix(brackets, brackets@.len()),
{
    if brackets@.len() == 0 {
        // base case: fold_left on empty sequence yields (0, true)
    } else {
        let n = brackets@.len();
        spec_bracketing_helper_prefix_equiv(brackets@.slice(0, n - 1));
        // By definition of fold_left and the recursive prefix definition, extending by the last character preserves equality
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
    /* code modified by LLM (iteration 5): iterate using tracked ghost counters and maintain invariant relating to spec prefix */
    let s = brackets;
    let tracked len: nat = s@.len();
    let tracked mut i: nat = 0;
    let tracked mut count: int = 0;
    let mut ok: bool = true;
    while i < len
        invariant
            i <= len,
            (count, ok) == spec_bracketing_prefix(s@, i),
        decreases
            len - i
    {
        let c = s@.index(i);
        match c {
            '(' => { count = count + 1; },
            ')' => {
                count = count - 1;
                if count < 0 {
                    ok = false;
                }
            },
            _ => { },
        }
        i = i + 1;
    }
    let res = ok && count == 0;
    proof {
        spec_bracketing_helper_prefix_equiv(s@);
    }
    res
}
// </vc-code>

}
fn main() {}