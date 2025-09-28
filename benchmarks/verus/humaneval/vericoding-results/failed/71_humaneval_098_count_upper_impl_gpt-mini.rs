// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_vowel(c: char) -> bool {
    c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O'
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate Vec runtime indexing and spec vowel predicate */
proof fn vec_index_is_upper_agree(s: Vec<char>, i: int)
    requires
        0 <= i && i < s@.len(),
    ensures
        is_upper_vowel(s@[i]) == (s[i as usize] == 'A' || s[i as usize] == 'E' || s[i as usize] == 'U' || s[i as usize] == 'I' || s[i as usize] == 'O'),
{
    proof {
        assert(s@[i] == s[i as usize]);
        assert(is_upper_vowel(s@[i]) == (s@[i] == 'A' || s@[i] == 'E' || s@[i] == 'U' || s@[i] == 'I' || s@[i] == 'O'));
        assert((s@[i] == 'A' || s@[i] == 'E' || s@[i] == 'U' || s@[i] == 'I' || s@[i] == 'O') == (s[i as usize] == 'A' || s[i as usize] == 'E' || s[i as usize] == 'U' || s[i as usize] == 'I' || s[i as usize] == 'O'));
        assert(is_upper_vowel(s@[i]) == (s[i as usize] == 'A' || s[i as usize] == 'E' || s[i as usize] == 'U' || s[i as usize] == 'I' || s[i as usize] == 'O'));
    }
}

// </vc-helpers>

// <vc-spec>
fn count_upper(s: Vec<char>) -> (cnt: usize)
    ensures cnt == Set::<int>::new(|i: int| 0 <= i < s@.len() && i % 2 == 0 && is_upper_vowel(s@[i])).len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate, check even indices and count uppercase vowels using helper */
    let mut idx: usize = 0;
    let mut res: usize = 0;
    while idx < s.len()
        invariant
            idx <= s.len(),
            res == Set::<int>::new(|j: int| 0 <= j < idx as int && j % 2 == 0 && is_upper_vowel(s@[j])).len(),
        decreases s.len() - idx
    {
        if idx % 2 == 0 {
            let c: char = s[idx];
            if c == 'A' || c == 'E' || c == 'U' || c == 'I' || c == 'O' {
                proof {
                    assert(0 <= idx as int);
                    assert(idx < s.len());
                    assert(idx as int < s@.len());
                    vec_index_is_upper_agree(s, idx as int);
                    assert(is_upper_vowel(s@[idx as int]));
                }
                res = res + 1;
            }
        }
        idx = idx + 1;
    }
    res
}

// </vc-code>


}

fn main() {}