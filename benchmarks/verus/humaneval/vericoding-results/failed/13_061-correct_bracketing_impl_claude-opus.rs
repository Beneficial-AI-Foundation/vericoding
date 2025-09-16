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
    /* code modified by LLM (iteration 5): use char iteration to avoid byte comparison issues */
    let mut depth: i32 = 0;
    let mut valid = true;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            i <= brackets.len(),
            depth >= 0,
            depth <= i as i32,
            depth >= -(i as i32),
            valid <==> spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
            depth == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
        decreases brackets.len() - i
    {
        let c = brackets.chars().nth(i).unwrap();
        if c == '(' {
            depth = depth + 1;
        } else if c == ')' {
            depth = depth - 1;
            if depth < 0 {
                valid = false;
            }
        }
        
        proof {
            let ghost_c = brackets@[i as int];
            assert(ghost_c == c);
            let prev = brackets@.subrange(0, i as int);
            let curr = brackets@.subrange(0, (i + 1) as int);
            assert(curr =~= prev.push(ghost_c));
        }
        
        i = i + 1;
    }
    
    assert(brackets@.subrange(0, brackets@.len() as int) =~= brackets@);
    valid && depth == 0
}
// </vc-code>

}
fn main() {}