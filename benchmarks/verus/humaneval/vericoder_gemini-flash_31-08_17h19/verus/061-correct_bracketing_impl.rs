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
spec fn spec_char_to_bracket_val(c: char) -> int {
    if c == '(' { 1 } else if c == ')' { -1 } else { 0 }
}

proof fn lemma_spec_char_to_bracket_val_sum(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        spec_bracketing_helper(s.subsequence(0, i + 1)).0 == spec_bracketing_helper(s.subsequence(0, i)).0 + spec_char_to_bracket_val(s[i]),
        spec_bracketing_helper(s.subsequence(0, i + 1)).1 == (spec_bracketing_helper(s.subsequence(0, i)).1 && (spec_bracketing_helper(s.subsequence(0, i)).0 + spec_char_to_bracket_val(s[i])) >= 0),
{
    let prev_prefix = s.subsequence(0, i);
    let current_char = s[i];
    let (prev_balance, prev_valid) = spec_bracketing_helper(prev_prefix);

    let next_char_val = spec_char_to_bracket_val(current_char);

    let (expected_balance, expected_valid) = match current_char {
        '(' => (prev_balance + 1, prev_valid),
        ')' => (prev_balance - 1, prev_valid && (prev_balance - 1 >= 0)),
        _ => (prev_balance, prev_valid),
    };

    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).0 == expected_balance);
    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == expected_valid);

    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).0 == prev_balance + next_char_val);

    match current_char {
        '(' => {
            assert(next_char_val == 1);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == prev_valid);
        },
        ')' => {
            assert(next_char_val == -1);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == (prev_valid && (prev_balance - 1 >= 0)));
        },
        _ => {
            assert(next_char_val == 0);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == prev_valid);
        },
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
    let mut balance: int = 0;
    let mut valid: bool = true;

    #[verifier(loop_invariant_param)]
    for i in 0..brackets.len()
        invariant
            0 <= i as int,
            i as int <= brackets.len(),
            balance == spec_bracketing_helper(brackets@.subsequence(0, i as int)).0,
            valid == spec_bracketing_helper(brackets@.subsequence(0, i as int)).1,
    {
        let c = brackets.as_bytes()[i] as char;

        proof {
            lemma_spec_char_to_bracket_val_sum(brackets@, i as int);
        }

        if c == '(' {
            balance = balance + 1;
        } else if c == ')' {
            balance = balance - 1;
        }

        if balance < 0 {
            valid = false;
        }
    }

    valid = valid && balance == 0;

    valid
}
// </vc-code>

} // verus!
fn main() {}