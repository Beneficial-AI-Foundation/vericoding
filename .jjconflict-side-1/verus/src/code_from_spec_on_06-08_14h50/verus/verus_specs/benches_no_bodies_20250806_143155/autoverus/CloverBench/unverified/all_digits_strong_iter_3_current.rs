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
    /* code modified by LLM (iteration 1): Fixed indexing to use usize for executable code and proper String iteration */
    let mut i = 0usize;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: nat| #![auto] j < i ==> is_ascii_digit_spec(s@[j as int]),
    {
        let c = s.as_bytes()[i] as char;
        if !is_ascii_digit(c) {
            return false;
        }
        i += 1;
    }
    true
}

} // verus!