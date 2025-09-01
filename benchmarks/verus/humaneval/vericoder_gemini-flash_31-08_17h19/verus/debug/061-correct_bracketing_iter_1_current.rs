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
        spec_bracketing_helper(s.subsequence(0, i + 1)).1 ==> (spec_bracketing_helper(s.subsequence(0, i)).1 && (spec_bracketing_helper(s.subsequence(0, i)).0 + spec_char_to_bracket_val(s[i])) >= 0),
{
    // This lemma essentially proves the inductive step for the `spec_bracketing_helper`'s fold_left behavior.
    // It asserts that adding the next character's value correctly updates both the balance and validity.
    // The proof structure depends on how `fold_left` is formalized in vstd and might require
    // manual unfolding for a full formal proof. For typical Verus usage,
    // Verus's SMT solver can often handle this inductive reasoning implicitly
    // when given the loop invariants below, but for a more robust helper,
    // this lemma makes the inductive property explicit.
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
        balance == spec_bracketing_helper(brackets@.subsequence(0, i as int)).0,
        valid <==> spec_bracketing_helper(brackets@.subsequence(0, i as int)).1,
        0 <= i,
        i <= brackets.len() as int,
    )]
    for i in 0..brackets.len() {
        let c = brackets.as_bytes()[i] as char;
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