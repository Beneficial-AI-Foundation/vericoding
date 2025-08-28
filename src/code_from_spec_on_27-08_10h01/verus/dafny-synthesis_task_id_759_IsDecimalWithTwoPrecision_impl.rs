use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_decimal_with_two_precision(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == '.' && s.len() - i - 1 == 2
}

proof fn lemma_decimal_found(s: Seq<char>, pos: int)
    requires
        0 <= pos < s.len(),
        s[pos] == '.',
        s.len() - pos - 1 == 2,
    ensures
        has_decimal_with_two_precision(s),
{
}

proof fn lemma_no_decimal_with_precision(s: Seq<char>)
    requires
        forall|i: int| 0 <= i < s.len() ==> !(s[i] == '.' && s.len() - i - 1 == 2),
    ensures
        !has_decimal_with_two_precision(s),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn is_decimal_with_two_precision(s: &str) -> (result: bool)
    ensures
        result ==> exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
        !result ==> !exists|i: int| 0 <= i < s@.len() && s@[i] == '.' && s@.len() - i - 1 == 2,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let s_seq = s@;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < i ==> !(s@[j] == '.' && s@.len() - j - 1 == 2),
    {
        if s@[i] == '.' && s.len() - i - 1 == 2 {
            proof {
                lemma_decimal_found(s@, i as int);
            }
            return true;
        }
        i += 1;
    }
    
    proof {
        lemma_no_decimal_with_precision(s@);
    }
    false
}
// </vc-code>

fn main() {
}

}