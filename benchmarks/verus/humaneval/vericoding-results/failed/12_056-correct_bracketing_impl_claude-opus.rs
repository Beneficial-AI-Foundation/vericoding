// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_bracketing_helper(brackets: Seq<char>) -> (result:(int, bool)) {
    brackets.fold_left(
        (0, true),
        |p: (int, bool), c|
            {
                let (x, b) = p;
                match (c) {
                    '<' => (x + 1, b),
                    '>' => (x - 1, b && x - 1 >= 0),
                    _ => (x, b),
                }
            },
    )
}

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// </vc-preamble>

// <vc-helpers>
proof fn fold_left_maintains_bounds(s: Seq<char>, i: nat)
    requires
        i <= s.len(),
        s.len() <= i32::MAX,
    ensures
        spec_bracketing_helper(s.subrange(0, i as int)).0 >= -i,
        spec_bracketing_helper(s.subrange(0, i as int)).0 <= i,
    decreases s.len() - i
{
    /* helper modified by LLM (iteration 5): unchanged helper function */
    if i == 0 {
        assert(s.subrange(0, 0) =~= Seq::<char>::empty());
        assert(spec_bracketing_helper(s.subrange(0, 0)) == (0int, true));
    } else {
        fold_left_maintains_bounds(s, (i - 1) as nat);
        let prev = s.subrange(0, (i - 1) as int);
        let curr = s.subrange(0, i as int);
        assert(curr =~= prev.push(s[(i - 1) as int]));
        let (prev_x, prev_b) = spec_bracketing_helper(prev);
        assert(prev_x >= -(i - 1));
        assert(prev_x <= i - 1);
        let c = s[(i - 1) as int];
        if c == '<' {
            assert(spec_bracketing_helper(curr).0 == prev_x + 1);
            assert(prev_x + 1 <= i);
            assert(prev_x + 1 >= -i);
        } else if c == '>' {
            assert(spec_bracketing_helper(curr).0 == prev_x - 1);
            assert(prev_x - 1 >= -i);
            assert(prev_x - 1 <= i);
        } else {
            assert(spec_bracketing_helper(curr).0 == prev_x);
        }
    }
}

fn get_char(s: &str, i: usize) -> (c: char)
    requires
        i < s@.len(),
    ensures
        c == s@[i as int],
{
    /* helper modified by LLM (iteration 5): unchanged helper to access string characters */
    s.chars().nth(i).unwrap()
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
    /* code modified by LLM (iteration 5): fixed cast by converting to usize properly */
    let mut depth: i32 = 0;
    let mut valid = true;
    let mut i: usize = 0;
    let len = brackets.len();

    while i < len
        invariant
            0 <= i <= brackets@.len(),
            len == brackets@.len(),
            brackets@.len() <= i32::MAX,
            -brackets@.len() >= i32::MIN,
            depth == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
            valid == spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
            depth >= -(i as i32),
            depth <= i as i32,
    {
        proof {
            fold_left_maintains_bounds(brackets@, i as nat);
        }
        
        let c = get_char(brackets, i);
        if c == '<' {
            depth = depth + 1;
        } else if c == '>' {
            depth = depth - 1;
            if depth < 0 {
                valid = false;
            }
        }
        
        i = i + 1;
        
        proof {
            let prev = brackets@.subrange(0, (i - 1) as int);
            let curr = brackets@.subrange(0, i as int);
            assert(curr =~= prev.push(brackets@[(i - 1) as int]));
            fold_left_maintains_bounds(brackets@, i as nat);
        }
    }
    
    assert(brackets@.subrange(0, brackets@.len() as int) =~= brackets@);
    valid && depth == 0
}
// </vc-code>

}
fn main() {}