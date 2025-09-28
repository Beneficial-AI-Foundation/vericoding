use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    let n: nat = s.len();
    if n == 0 {
        return false;
    }
    let mut i: nat = 0;
    while i < n
        invariant i <= n && (forall|j: int| 0 <= j && j < i as int ==> is_digit(s@[j]));
        decreases n - i;
    {
        if !is_digit(s@[i as int]) {
            return false;
        }
        i += 1;
    }
    assert(i == n);
    assert(forall|j: int| 0 <= j && j < n as int ==> is_digit(s@[j]));
    true
}
// </vc-code>

fn main() {
}

}