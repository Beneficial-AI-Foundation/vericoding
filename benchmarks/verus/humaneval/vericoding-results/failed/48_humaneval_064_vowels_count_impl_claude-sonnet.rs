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
/* helper modified by LLM (iteration 5): added exec function is_vowel_exec to call from exec code */
exec fn is_vowel_exec(c: char) -> (result: bool)
    ensures result == is_vowel(c)
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

proof fn count_vowels_append(s1: Seq<char>, s2: Seq<char>)
    ensures count_vowels(s1 + s2) == count_vowels(s1) + count_vowels(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
        assert(s1 + s2 =~= s2);
    } else {
        let rest = s1.subrange(1, s1.len() as int);
        assert((s1 + s2).subrange(1, (s1 + s2).len() as int) =~= rest + s2);
        count_vowels_append(rest, s2);
    }
}

proof fn count_vowels_subrange(s: Seq<char>, i: int)
    requires 0 <= i < s.len()
    ensures count_vowels(s) == count_vowels(s.subrange(0, i)) + count_vowels(s.subrange(i, s.len() as int))
{
    count_vowels_append(s.subrange(0, i), s.subrange(i, s.len() as int));
    assert(s.subrange(0, i) + s.subrange(i, s.len() as int) =~= s);
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
    /* code modified by LLM (iteration 5): added overflow checks and fixed invariant to track total count including y */
    let mut count = 0u8;
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_vowels(s@.subrange(0, i as int)),
            count as int <= i,
        decreases s.len() - i
    {
        if is_vowel_exec(s[i]) {
            assert(count < 255);
            count = count + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, i as int) =~= s@);
    }
    
    if s.len() > 0 && s[s.len() - 1] == 'y' {
        assert(count < 255);
        count = count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}