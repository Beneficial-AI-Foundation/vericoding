use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn is_digit_char(c: char) -> bool {
    c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
    c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn all_digits(s: &str) -> (result: bool)
    ensures result <==> (forall|i: int| 0 <= i < s@.len() ==> {
        let c = #[trigger] s@.index(i);
        c == '0' || c == '1' || c == '2' || c == '3' || c == '4' || 
        c == '5' || c == '6' || c == '7' || c == '8' || c == '9'
    })
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < s@.len()
        invariant
            0 <= i <= s@.len(),
            forall|j: int| 0 <= j < i ==> is_digit_char(s@.index(j))
    {
        let c = s@.index(i as int);
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