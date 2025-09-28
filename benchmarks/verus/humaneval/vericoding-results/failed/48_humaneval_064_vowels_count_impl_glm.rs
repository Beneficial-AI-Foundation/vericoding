// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

spec fn count_vowels(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        count_vowels(s.subrange(1, s.len() as int)) + (if is_vowel(s[0]) { 1int } else { 0int })
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Made is_vowel_exec a spec function */
spec fn is_vowel_exec(c: char) -> bool {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

proof fn is_vowel_exec_equiv(c: char)
    ensures
        is_vowel_exec(c) == is_vowel(c)
{
    assert(is_vowel_exec(c) == is_vowel(c));
}
// </vc-helpers>

// <vc-spec>
fn vowel_count(s: &Vec<char>) -> (count: u8)
  ensures
    count as int >= 0,
    count as int == count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Updated to use spec function instead of exec function */
{
    let mut count: u32 = 0;
    let n = s.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            count as int == count_vowels(s@.subrange(0, i as int)),
        decreases n - i
    {
        let c = s[i];
        let is_v = is_vowel(c);
        if is_v {
            count += 1;
        }
        i += 1;
    }
    if n > 0 && s[n-1] == 'y' {
        count += 1;
    }
    count as u8
}
// </vc-code>


}

fn main() {}