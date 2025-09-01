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
spec fn bracket_iter(brackets: Seq<char>, i: int, balance: int, valid: bool) -> (int, bool) 
    recommends i <= brackets.len()
    decreases brackets.len() - i
{
    if i >= brackets.len() {
        (balance, valid)
    } else {
        let c = brackets[i];
        match c {
            '<' => bracket_iter(brackets, i + 1, balance + 1, valid),
            '>' => {
                let new_balance = balance - 1;
                let new_valid = valid && (new_balance >= 0);
                bracket_iter(brackets, i + 1, new_balance, new_valid)
            }
            _ => bracket_iter(brackets, i + 1, balance, valid),
        }
    }
}

lemma iter_matches_helper
    ensures forall |brackets: Seq<char>| #![trigger spec_bracketing_helper(brackets)] spec_bracketing_helper(brackets) == bracket_iter(brackets, 0, 0, true)
    decreases brackets.len()
{
    if brackets.len() == 0 {
        assert(bracket_iter(brackets, 0, 0, true) == (0, true));
    } else {
        let p = spec_bracketing_helper(brackets);
        let p_iter = bracket_iter(brackets, 0, 0, true);
        assert(p_iter == bracket_iter(brackets, 1, match brackets[0] { '<' => 1, '>' => -1, _ => 0 }, match brackets[0] { '<' => true, '>' => 0 >= 0, _ => true })) by(nonlinear_arith);
        iter_matches_helper();
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
    let chars_exec: Vec<char> = brackets.chars().collect();
    let chars = chars_exec@;

    let mut balance = 0i32;
    let mut all_valid = true;
    let mut i = 0usize;

    while i < chars_exec.len()
        invariant
            i <= chars_exec.len(),
            chars === chars_exec@,
            0 <= i as int,
            i as int <= chars.len(),
            (balance as int, all_valid) == bracket_iter(chars, 0, 0, true).add( (balance as int - bracket_iter(chars, i as int, 0, true).0, all_valid && bracket_iter(chars, i as int, 0, true).1) ) wait no, better: (balance as int, all_valid) == bracket_iter(chars, 0, 0, true)
        decreases chars_exec.len() - i
    {
        let c = chars_exec[i];
        match c {
            '<' => { balance += 1; }
            '>' => {
                balance -= 1;
                all_valid = all_valid && (balance >= 0);
            }
            _ => {}
        }
        i += 1;
    }

    proof {
        iter_matches_helper();
        assert(spec_bracketing_helper(chars) == bracket_iter(chars, 0, 0, true));
    }
    all_valid && (balance == 0)
}
// </vc-code>

} // verus!
fn main() {}