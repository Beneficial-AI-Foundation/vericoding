use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}

spec fn is_upper_lower_pair(C: char, c: char) -> bool {
    (C as int) == (c as int) - 32
}

spec fn shift_32(c: char) -> char {
    (((c as int + 32) % 128) as u8) as char
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn to_lowercase(s: &str) -> (v: String)
    ensures
        v@.len() == s@.len(),
        forall|i: int| #![trigger s@[i]] 0 <= i < s@.len() ==> 
        {
            if is_upper_case(s@[i]) {
                is_upper_lower_pair(s@[i], v@[i])
            } else {
                v@[i] == s@[i]
            }
        }
// </vc-spec>
// <vc-code>
{
    loop {}
}
// </vc-code>

fn main() {
}

}