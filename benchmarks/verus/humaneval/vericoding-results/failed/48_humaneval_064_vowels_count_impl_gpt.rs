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
/* helper modified by LLM (iteration 2): lemma for stepping count_vowels over a tail slice */
proof fn lemma_count_vowels_tail_step(s: Seq<char>, i: int, j: int)
    requires
        0 <= i,
        i < j,
        j <= s.len(),
    ensures
        count_vowels(s.subrange(i, j)) == count_vowels(s.subrange(i + 1, j)) + (if is_vowel(s[i]) { 1int } else { 0int }),
    decreases j - i
{
    let t = s.subrange(i, j);
    assert(t.len() == j - i);
    assert(t.len() > 0);
    assert(t[0] == s[i]);
    assert(t.subrange(1, t.len()) == s.subrange(i + 1, j));
}

// </vc-helpers>

// <vc-spec>
fn vowel_count(s: &Vec<char>) -> (count: u8)
  ensures
    count as int >= 0,
    count as int == count_vowels(s@) + (if s@.len() > 0 && s@[s@.len() - 1] == 'y' { 1int } else { 0int })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): remove int-suffixed literals; maintain loop invariant accumulating vowel count from tail */
    let len = s.len();
    let mut i: usize = len;
    let mut acc: int = 0;
    while i > 0
        invariant
            i <= len,
            acc == count_vowels(s@.subrange(i as int, len as int)),
        decreases i
    {
        let j = i - 1;
        let c = s[j];
        proof {
            lemma_count_vowels_tail_step(s@, j as int, len as int);
        }
        if is_vowel(c) {
            acc = acc + 1;
        }
        i = j;
    }
    proof {
        assert(s@.subrange(0, len as int) == s@);
    }
    let plus_y: int = if len > 0 && s[len - 1] == 'y' { 1 } else { 0 };
    let total: int = acc + plus_y;
    let result: u8 = total as u8;
    result
} 

// </vc-code>


}

fn main() {}