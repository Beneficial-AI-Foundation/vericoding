use vstd::prelude::*;

fn main() {}
verus! {

spec fn is_ascii_digit_spec(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

fn is_ascii_digit(c: char) -> (r: bool)
    ensures
        r == is_ascii_digit_spec(c),
{
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || c == '5' || c == '6' || c == '7'
        || c == '8' || c == '9'
}

spec fn all_digits_spec(s: Seq<char>) -> bool {
    forall|i: nat| #![auto] i < s.len() ==> is_ascii_digit_spec(s[i as int])
}

fn all_digits(s: String) -> (result: bool)
    requires
        s.is_ascii(),
    ensures
        all_digits_spec(s@) == result,
{
    let mut i: usize = 0;
    let s_view = s@;
    /* code modified by LLM (iteration 1): Use usize indexing instead of int casting for executable code */
    while i < s_view.len()
        invariant
            0 <= i <= s_view.len(),
            s_view == s@,
            forall|j: nat| #![auto] j < i ==> is_ascii_digit_spec(s_view[j as int]),
    {
        let c = s_view[i];
        if !is_ascii_digit(c) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!