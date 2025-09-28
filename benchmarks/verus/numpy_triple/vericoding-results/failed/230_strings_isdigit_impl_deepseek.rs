// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove duplicate spec declaration and keep only one implementation */
spec fn all_chars_digit(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> ('0' <= s[i] && s[i] <= '9')
}

proof fn lemma_all_chars_digit_empty()
    ensures
        all_chars_digit(Seq::empty()),
{
}

proof fn lemma_all_chars_digit_push(s: Seq<char>, c: char)
    requires
        all_chars_digit(s),
        '0' <= c <= '9',
    ensures
        all_chars_digit(s.push(c)),
{
}

proof fn lemma_all_chars_digit_pop(s: Seq<char>)
    requires
        s.len() > 0,
        all_chars_digit(s),
    ensures
        all_chars_digit(s.subrange(0, s.len() - 1)),
{
}
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == (a[i as int]@.len() > 0 && all_chars_digit(a[i as int]@))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix verification issues with proper spec function definition */
{
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (a[j]@.len() > 0 && all_chars_digit(a[j]@)),
    {
        let s = a.index(i);
        let s_seq = s@;
        let is_digit = if s_seq.len() == 0 {
            false
        } else {
            let mut all_digits = true;
            let mut j: usize = 0;
            
            while j < s_seq.len()
                invariant
                    j <= s_seq.len(),
                    all_digits == (forall|k: int| 0 <= k < j ==> ('0' <= s_seq[k] && s_seq[k] <= '9')),
            {
                if !('0' <= s_seq[j] && s_seq[j] <= '9') {
                    all_digits = false;
                    break;
                }
                j = j + 1;
            }
            all_digits
        };
        
        result.push(is_digit);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}