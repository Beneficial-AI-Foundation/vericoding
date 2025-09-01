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
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (ret:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn fold_left_bracketing_helper_monotonic(brackets: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= brackets.len(),
    ensures
        spec_bracketing_helper(brackets.subrange(0, i)).0 <= spec_bracketing_helper(brackets.subrange(0, j)).0 + (j - i),
        spec_bracketing_helper(brackets.subrange(0, j)).0 <= spec_bracketing_helper(brackets.subrange(0, i)).0 + (j - i),
{
    if i < j {
        let c = brackets@[i];
        let (x_i, b_i) = spec_bracketing_helper(brackets.subrange(0, i));
        let (x_j, b_j) = spec_bracketing_helper(brackets.subrange(0, i+1));
        match c {
            '(' => assert(x_j == x_i + 1),
            ')' => assert(x_j == x_i - 1),
            _ => assert(x_j == x_i),
        };
        fold_left_bracketing_helper_monotonic(brackets, i+1, j);
    }
}

proof fn fold_left_bracketing_helper_nonneg(brackets: Seq<char>, i: int)
    requires
        0 <= i <= brackets.len(),
        spec_bracketing_helper(brackets.subrange(0, i)).1,
    ensures
        spec_bracketing_helper(brackets.subrange(0, i)).0 >= 0,
{
    if i > 0 {
        let prev = spec_bracketing_helper(brackets.subrange(0, i-1));
        let curr = spec_bracketing_helper(brackets.subrange(0, i));
        let c = brackets@[i-1];
        fold_left_bracketing_helper_nonneg(brackets, i-1);
        assert(prev.1 && prev.0 >= 0);
        match c {
            '(' => assert(curr.0 == prev.0 + 1),
            ')' => assert(curr.0 == prev.0 - 1 && curr.1 == (prev.1 && prev.0 - 1 >= 0)),
            _ => assert(curr.0 == prev.0),
        };
    }
}

proof fn spec_bracketing_helper_append(brackets: Seq<char>, c: char)
    ensures
        spec_bracketing_helper(brackets.push(c)) == {
            let (x, b) = spec_bracketing_helper(brackets);
            match c {
                '(' => (x + 1, b),
                ')' => (x - 1, b && x - 1 >= 0),
                _ => (x, b),
            }
        },
{
}
// </vc-helpers>

// <vc-spec>
fn correct_bracketing(brackets: &str) -> (ret: bool)
    // pre-conditions-start
    requires
        brackets@.len() <= i32::MAX,
        -brackets@.len() >= i32::MIN,
    // pre-conditions-end
    // post-conditions-start
    ensures
        ret <==> spec_bracketing(brackets@),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut count: int = 0;
    let mut valid: bool = true;
    let len: usize = brackets.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            i <= len,
            count == spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
            valid == spec_bracketing_helper(brackets@.subrange(0, i as int)).1,
            count >= 0,
    {
        let c = brackets.as_bytes()[i] as char;
        proof {
            fold_left_bracketing_helper_nonneg(brackets@.subrange(0, i as int), i as int);
            spec_bracketing_helper_append(brackets@.subrange(0, i as int), c);
        }
        match c {
            '(' => {
                count = count + 1;
            }
            ')' => {
                count = count - 1;
                valid = valid && count >= 0;
            }
            _ => {}
        }
        i = i + 1;
    }
    
    proof {
        assert(count == spec_bracketing_helper(brackets@).0);
        assert(valid == spec_bracketing_helper(brackets@).1);
        assert(spec_bracketing(brackets@) == (spec_bracketing_helper(brackets@).1 && spec_bracketing_helper(brackets@).0 == 0));
    }
    
    valid && count == 0
}
// </vc-code>

} // verus!
fn main() {}