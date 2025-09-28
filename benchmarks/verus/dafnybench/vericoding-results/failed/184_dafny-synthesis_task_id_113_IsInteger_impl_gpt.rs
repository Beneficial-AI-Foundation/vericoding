use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>
spec fn all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit(s[i])
}

spec fn nonempty(s: Seq<char>) -> bool {
    s.len() > 0
}
// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
}
// </vc-code>

fn main() {
}

}