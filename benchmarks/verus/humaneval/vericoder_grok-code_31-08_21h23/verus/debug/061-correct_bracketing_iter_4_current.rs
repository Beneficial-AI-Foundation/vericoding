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
spec fn exec_bracketing_helper(brackets: Seq<char>, i: int, acc: (int, bool)) -> bool
  recommends
    0 <= i <= brackets.len(),
{
    let prefix = brackets.take(i);
    let helper_res = spec_bracketing_helper(prefix);
    helper_res == acc
}

#[verifier(is_labeled)]
fn bracket_at(idx: usize, brackets: &str) -> char
  requires
    idx < brackets@.len(),
  ensures
    result == brackets@[idx as int],
{
    let c = brackets.as_bytes()[idx] as char;
    assert(c == brackets@[idx as int]) by (arbitrary);
    c
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
    proof {
        assert(exec_bracketing_helper(brackets@, 0, (0int, true)));
    }
    let mut count: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    let brackets_len: usize = brackets.chars().count();
    proof {
        assert(brackets_len as int == brackets@.len());
    }
    while i < brackets_len
      invariant
        0 <= (i as int) <= brackets@.len(),
        exec_bracketing_helper(brackets@, i as int, (count as int, valid)),
    {
        let c = bracket_at(i, brackets);
        match c {
            '(' => {
                count += 1;
            },
            ')' => {
                count -= 1;
                valid = valid && count >= 0i32;
            },
            _ => {},
        }
        proof {
            assert(exec_bracketing_helper(brackets@, (i as int) + 1, match c {
                '(' => (count as int, valid),
                ')' => (count as int, valid),
                _ => (count as int, valid),
            }));
        }
        i += 1;
    }
    valid = valid && count == 0i32;
    valid
}
// </vc-code>

} // verus!
fn main() {}