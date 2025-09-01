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
    // The proof for this lemma requires unfolding the definition of spec_bracketing_helper for a single step.
    // Verus's SMT solver can often handle this inductive reasoning implicitly when given the
    // loop invariants. Below is a detailed, manual proof demonstrating the reasoning.

    let prev_prefix = s.subsequence(0, i);
    let current_char = s[i];
    let (prev_balance, prev_valid) = spec_bracketing_helper(prev_prefix);

    let next_char_val = spec_char_to_bracket_val(current_char);

    let (expected_balance, expected_valid) = match current_char {
        '(' => (prev_balance + 1, prev_valid),
        ')' => (prev_balance - 1, prev_valid && (prev_balance - 1 >= 0)),
        _ => (prev_balance, prev_valid),
    };

    // This is the core reasoning of fold_left applied to a single step.
    // The spec_bracketing_helper definition uses fold_left, so this mirrors its behavior.
    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).0 == expected_balance);
    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == expected_valid);

    // Now prove the 'ensures' clauses based on the definition of next_char_val
    assert(spec_bracketing_helper(s.subsequence(0, i + 1)).0 == prev_balance + next_char_val);

    // For the second `ensures` clause:
    match current_char {
        '(' => {
            assert(next_char_val == 1);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == prev_valid);
            assert((prev_valid && (prev_balance + 1 >= 0)) == prev_valid); // Since prev_valid is already established, and prev_balance doesn't become negative from +1
        },
        ')' => {
            assert(next_char_val == -1);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == (prev_valid && (prev_balance - 1 >= 0)));
            assert((prev_valid && (prev_balance - 1 >= 0)) == (prev_valid && (prev_balance + next_char_val >= 0)));
        },
        _ => {
            assert(next_char_val == 0);
            assert(spec_bracketing_helper(s.subsequence(0, i + 1)).1 == prev_valid);
            assert((prev_valid && (prev_balance + 0 >= 0)) == prev_valid);
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
    let mut balance: i64 = 0;
    let mut valid: bool = true;

    #[invariant(
        i <= brackets.len() as int,
        balance == spec_bracketing_helper(brackets@.subsequence(0, i as int)).0,
        valid == spec_bracketing_helper(brackets@.subsequence(0, i as int)).1,
    )]
    for i in 0..brackets.len() {
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

    // At the end of the loop, balance and valid reflect the state for the full sequence.
    // We need to check if the final balance is zero and if it remained valid throughout.
    valid = valid && balance == 0;

    valid
}
// </vc-code>

} // verus!
fn main() {}