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
    let n = s.len();
    if n == 0 {
        return false;
    }
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall|j: int| 0 <= j < i ==> { is_digit(s@[j]) }
    {
        if !is_digit(s@[i]) {
            return false;
        }
        let ghost i_prev = i;
        i += 1;
        assert forall|j: int| 0 <= j < i ==> { is_digit(s@[j]) } by {
            if j < i_prev {
                assert(is_digit(s@[j]));
            } else {
                assert(j == i_prev);
                assert(is_digit(s@[j]));
            }
        }
    }
    true
}
// </vc-code>

fn main() {
}

}