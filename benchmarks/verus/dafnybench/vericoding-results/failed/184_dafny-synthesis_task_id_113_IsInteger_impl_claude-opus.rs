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
    if s.len() == 0 {
        return false;
    }
    
    let s_vec = s.to_vec();
    let mut i: usize = 0;
    while i < s_vec.len()
        invariant
            s_vec@ == s,
            0 <= i <= s_vec.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] is_digit(s[j]),
    {
        if !is_digit(s_vec[i] as char) {
            assert(!is_digit(s[i as int]));
            assert(!(forall|k: int| 0 <= k < s.len() ==> is_digit(s[k])));
            return false;
        }
        i = i + 1;
    }
    
    assert(i == s.len());
    assert(forall|j: int| 0 <= j < s.len() ==> is_digit(s[j]));
    true
}
// </vc-code>

fn main() {
}

}