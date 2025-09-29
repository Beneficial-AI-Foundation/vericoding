use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_digit_char(c: char) -> (result: bool)
    ensures result <==> (c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
                        c == '5' || c == '6' || c == '7' || c == '8' || c == '9')
{
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
    c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}

#[verifier::external_body]
fn str_len_exec(s: &str) -> (result: usize)
    ensures result as nat == s@.len()
{
    s.len()
}

#[verifier::external_body]
fn str_char_at(s: &str, i: usize) -> (result: char)
    requires i < s@.len()
    ensures result == s@.index(i as int)
{
    s.chars().nth(i).unwrap()
}
// </vc-helpers>

// <vc-spec>
fn all_digits(s: &str) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < s@.len() ==> {
        let c = #[trigger] s@.index(i);
        c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
        c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
    })
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    let len = str_len_exec(s);
    while i < len
        invariant
            0 <= i <= s@.len(),
            len as nat == s@.len(),
            forall|j: int| 0 <= j < i ==> {
                let c = #[trigger] s@.index(j);
                c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
                c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
            }
        decreases len - i
    {
        let c = str_char_at(s, i);
        if !is_digit_char(c) {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {
}

}