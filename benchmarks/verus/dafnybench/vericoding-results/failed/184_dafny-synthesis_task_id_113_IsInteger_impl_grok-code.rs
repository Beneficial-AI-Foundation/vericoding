use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    let len_exec = s.len();
    let mut is_all_digits = true;
    let mut i: usize = 0;
    while i < len_exec
        invariant
            0 <= i as int <= s.@len() as int,
            is_all_digits <==> (forall|j: int| 0 <= j < i as int ==> is_digit(s@[j]))
    {
        if !is_digit(s@[i]) {
            is_all_digits = false;
        }
        i += 1;
    }
    let result = (s.@len() > 0) && is_all_digits;
    result
}
// </vc-code>

fn main() {
}

}