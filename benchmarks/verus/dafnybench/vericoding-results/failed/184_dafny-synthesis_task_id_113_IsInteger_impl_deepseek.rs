use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>
spec fn is_digit_char(c: char) -> bool {
    48 <= c as int <= 57
}

proof fn all_chars_are_digits(s: Seq<char>, n: nat)
    requires
        n <= s.len(),
        forall|i: int| 0 <= i < n ==> is_digit(s[i])
    ensures
        forall|i: int| 0 <= i < n ==> #[trigger] is_digit(s[i])
{
    if n > 0 {
        all_chars_are_digits(s.subrange(0, n - 1), (n - 1) as nat);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// <vc-code>
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_digit(s[j])
    {
        let c: char = s[i];
        proof {
            assert(is_digit(c) == (48 <= c as int <= 57));
        }
        if !is_digit(c) {
            return false;
        }
        i = i + 1;
    }
    
    proof {
        all_chars_are_digits(s, s.len());
    }
    
    true
}
// </vc-code>

fn main() {
}

}