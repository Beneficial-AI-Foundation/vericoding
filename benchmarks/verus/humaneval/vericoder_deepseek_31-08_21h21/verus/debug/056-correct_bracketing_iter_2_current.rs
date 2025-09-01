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
// pure-end
// pure-end

spec fn spec_bracketing(brackets: Seq<char>) -> (result:bool) {
    let p = spec_bracketing_helper(brackets);
    p.1 && p.0 == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_bracketing_helper_nonneg(brackets: Seq<char>, i: int, x: int, b: bool)
    requires
        0 <= i <= brackets.len(),
        spec_bracketing_helper(brackets.subrange(0, i)) == (x, b),
    ensures
        x >= 0,
{
    if i == 0 {
        assert(x == 0);
    } else {
        let prev = spec_bracketing_helper(brackets.subrange(0, i - 1));
        lemma_bracketing_helper_nonneg(brackets, i - 1, prev.0, prev.1);
        match brackets[i - 1] {
            '<' => assert(x == prev.0 + 1),
            '>' => assert(x == prev.0 - 1),
            _ => assert(x == prev.0),
        };
    }
}

proof fn lemma_bracketing_helper_monotonic(brackets: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= brackets.len(),
    ensures
        spec_bracketing_helper(brackets.subrange(0, i)).0 <= spec_bracketing_helper(brackets.subrange(0, j)).0 + (j - i),
{
    if i < j {
        lemma_bracketing_helper_monotonic(brackets, i, j - 1);
        let prev = spec_bracketing_helper(brackets.subrange(0, j - 1));
        match brackets[j - 1] {
            '<' => assert(spec_bracketing_helper(brackets.subrange(0, j)).0 == prev.0 + 1),
            '>' => assert(spec_bracketing_helper(brackets.subrange(0, j)).0 == prev.0 - 1),
            _ => assert(spec_bracketing_helper(brackets.subrange(0, j)).0 == prev.0),
        };
    }
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
    let mut count = 0;
    let mut valid = true;
    let n = brackets.len();
    let chars: Vec<char> = brackets.chars().collect();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            count is int,
            count == spec_bracketing_helper(chars@.subrange(0, i as int)).0,
            valid == spec_bracketing_helper(chars@.subrange(0, i as int)).1,
            count >= 0,
    {
        let c = chars[i];
        match c {
            '<' => {
                count = count + 1;
            }
            '>' => {
                if count > 0 {
                    count = count - 1;
                } else {
                    valid = false;
                }
            }
            _ => {}
        }
        i = i + 1;
    }
    valid && count == 0
}
// </vc-code>

} // verus!
fn main() {}