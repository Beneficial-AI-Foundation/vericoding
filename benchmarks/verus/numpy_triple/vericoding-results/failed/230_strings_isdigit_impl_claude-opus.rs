// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == (a[i as int]@.len() > 0 && all_chars_digit(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type error and remove duplicate spec definition */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j as int] == (a[j as int]@.len() > 0 && all_chars_digit(a[j as int]@))
    {
        let s = &a[i];
        let s_seq = s@;
        let mut all_digits = s_seq.len() > 0;
        
        if all_digits {
            let mut j: usize = 0;
            while j < s_seq.len()
                invariant
                    0 <= j <= s_seq.len(),
                    all_digits == (forall|k: int| 0 <= k < j ==> s_seq[k as int].is_ascii_digit()),
                    s_seq.len() > 0
            {
                if !s_seq[j as int].is_ascii_digit() {
                    all_digits = false;
                    assert(!s_seq[j as int].is_ascii_digit());
                    assert(exists|k: int| 0 <= k < s_seq.len() && !s_seq[k].is_ascii_digit());
                }
                j = j + 1;
            }
            assert(all_digits == (forall|k: int| 0 <= k < s_seq.len() ==> s_seq[k].is_ascii_digit()));
            assert(all_digits == all_chars_digit(s_seq));
        }
        
        assert(all_digits == (s_seq.len() > 0 && all_chars_digit(s_seq)));
        result.push(all_digits);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}