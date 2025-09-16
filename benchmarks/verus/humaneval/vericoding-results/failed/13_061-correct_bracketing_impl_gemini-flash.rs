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
/* helper modified by LLM (iteration 5): removed */
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
/* code modified by LLM (iteration 5): Corrected type issues with 'nat' and 'int' in invariants and loop condition by casting to 'usize' where appropriate for concrete code, and keeping 'int' for ghost values. */
{
    let mut x: int = 0;
    let mut b: bool = true;

    let s: Seq<char> = brackets@;

    let mut i: usize = 0;
    while (i as int) < s.len()
        invariant 
            0 <= i as int,
            i as int <= s.len(),
            b == s.subsequence(0, i as nat).fold_left((0, true), |p: (int, bool), c| {
                let (x_local, b_local) = p;
                match (c) {
                    '(' => (x_local + 1, b_local),
                    ')' => (x_local - 1, b_local && x_local - 1 >= 0),
                    _ => (x_local, b_local),
                }
            }).1,
            x == s.subsequence(0, i as nat).fold_left((0, true), |p: (int, bool), c| {
                let (x_local, b_local) = p;
                match (c) {
                    '(' => (x_local + 1, b_local),
                    ')' => (x_local - 1, b_local && x_local - 1 >= 0),
                    _ => (x_local, b_local),
                }
            }).0,
            x <= i as int,
            x >= -(i as int),

        decreases
            s.len() - (i as int),
    {
        match s.index(i as nat) {
            '(' => {
                x = x + 1;
            },
            ')' => {
                x = x - 1;
                if x < 0 {
                    b = false;
                }
            },
            _ => {},
        }

        i = i + 1;
    }
    b && (x == 0)
}
// </vc-code>

}
fn main() {}