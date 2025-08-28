use vstd::prelude::*;

verus! {

spec fn is_digit(c: char) -> bool {
    48 <= c as int <= 57
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_integer(s: Seq<char>) -> (result: bool)
    ensures result <==> (s.len() > 0) && (forall|i: int| 0 <= i < s.len() ==> is_digit(s[i]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if s.len() == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> is_digit(s[j])
    {
        if !is_digit(s[i as int]) {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}