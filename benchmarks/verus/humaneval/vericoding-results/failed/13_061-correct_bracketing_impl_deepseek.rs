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
/* helper modified by LLM (iteration 5): Fixed type mismatches in parameter and calls */
proof fn helper_lemma(brackets: Seq<char>, i: nat) 
    requires 
        0 <= i <= brackets.len(),
    ensures 
        spec_bracketing_helper(brackets.subrange(0, i as int)) == brackets.subrange(0, i as int).fold_left((0, true), |p: (int, bool), c| {
            let (x, b) = p;
            match c {
                '(' => (x + 1, b),
                ')' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        }),
    decreases brackets.len() - i,
{
    if i > 0 {
        helper_lemma(brackets.subrange(0, (i - 1) as nat), (i - 1) as nat);
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
/* code modified by LLM (iteration 5): Fixed all type mismatches and simplified implementation */
{
    let s = brackets@;
    let mut balance = 0;
    let mut valid = true;
    
    for i in 0..s.len()
        invariant
            0 <= balance,
            valid ==> spec_bracketing_helper(s.subrange(0, i as int)).1,
            balance == spec_bracketing_helper(s.subrange(0, i as int)).0,
    {
        let c = s[i as int];
        match c {
            '(' => {
                balance = balance + 1;
            }
            ')' => {
                if balance > 0 {
                    balance = balance - 1;
                } else {
                    valid = false;
                }
            }
            _ => {}
        }
    }
    
    valid && balance == 0
}
// </vc-code>

}
fn main() {}