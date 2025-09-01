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
proof fn lemma_fold_left_helper(brackets: Seq<char>, i: int)
    requires 0 <= i <= brackets.len()
    ensures ({
        let partial = brackets.subrange(0, i);
        let (count, valid) = spec_bracketing_helper(partial);
        valid ==> count >= 0
    })
{
    if i == 0 {
        assert(brackets.subrange(0, 0) == Seq::<char>::empty());
    } else {
        lemma_fold_left_helper(brackets, i - 1);
        let prev = brackets.subrange(0, i - 1);
        let curr = brackets.subrange(0, i);
        assert(curr == prev.push(brackets[i - 1]));
    }
}

proof fn lemma_fold_left_monotonic(brackets: Seq<char>, i: int, count: int, valid: bool)
    requires 
        0 <= i < brackets.len(),
        (count, valid) == spec_bracketing_helper(brackets.subrange(0, i)),
        valid
    ensures ({
        let next_char = brackets[i];
        let (new_count, new_valid) = match next_char {
            '(' => (count + 1, valid),
            ')' => (count - 1, valid && count - 1 >= 0),
            _ => (count, valid),
        };
        (new_count, new_valid) == spec_bracketing_helper(brackets.subrange(0, i + 1))
    })
{
    let partial = brackets.subrange(0, i);
    let extended = brackets.subrange(0, i + 1);
    assert(extended == partial.push(brackets[i]));
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
    let mut count: i32 = 0;
    let mut valid: bool = true;
    let mut i: usize = 0;
    
    while i < brackets.len()
        invariant
            0 <= i <= brackets.len(),
            brackets@.len() <= i32::MAX,
            -brackets@.len() >= i32::MIN,
            ({
                let partial = brackets@.subrange(0, i as int);
                let (spec_count, spec_valid) = spec_bracketing_helper(partial);
                count == spec_count && valid == spec_valid
            }),
            valid ==> count >= 0,
    {
        proof {
            lemma_fold_left_helper(brackets@, i as int);
        }
        
        let c = brackets.as_bytes()[i];
        let char_val = c as char;
        match char_val {
            '(' => {
                count = count + 1;
            },
            ')' => {
                count = count - 1;
                if count < 0 {
                    valid = false;
                }
            },
            _ => {},
        }
        
        proof {
            lemma_fold_left_monotonic(brackets@, i as int, 
                spec_bracketing_helper(brackets@.subrange(0, i as int)).0,
                spec_bracketing_helper(brackets@.subrange(0, i as int)).1);
        }
        
        i = i + 1;
    }
    
    assert(brackets@.subrange(0, brackets@.len() as int) == brackets@);
    valid && count == 0
}
// </vc-code>

} // verus!
fn main() {}