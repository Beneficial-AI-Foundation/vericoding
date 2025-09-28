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
/* helper modified by LLM (iteration 5): Fixed lemma with proper recursion and added bounds helper */
fn is_vowel_exec(c: char) -> (result: bool)
    ensures
        result == is_vowel(c),
{
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
}

proof fn lemma_count_vowels_subrange(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        count_vowels(s.subrange(i, j)) == count_vowels(s.subrange(0, j)) - count_vowels(s.subrange(0, i)),
    decreases j - i
{
    if i == j {
        assert(s.subrange(i, j) =~= Seq::<char>::empty());
        assert(count_vowels(Seq::<char>::empty()) == 0);
    } else if i == 0 {
        assert(s.subrange(0, i) =~= Seq::<char>::empty());
        assert(count_vowels(Seq::<char>::empty()) == 0);
        assert(s.subrange(i, j) =~= s.subrange(0, j));
    } else {
        assert(s.subrange(0, i).len() > 0);
        assert(s.subrange(0, j).len() > 0);
        let c = s[0];
        assert(s.subrange(0, i) =~= seq![c] + s.subrange(1, i));
        assert(s.subrange(0, j) =~= seq![c] + s.subrange(1, j));
        assert(s.subrange(i, j) =~= s.subrange(1, j).subrange(i - 1, j - 1));
        lemma_count_vowels_subrange(s.subrange(1, s.len() as int), i - 1, j - 1);
    }
}

proof fn lemma_count_from_index(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        count_vowels(s.subrange(0, i)) + count_vowels(s.subrange(i, s.len() as int)) == count_vowels(s),
{
    lemma_count_vowels_subrange(s, 0, s.len() as int);
    lemma_count_vowels_subrange(s, i, s.len() as int);
    assert(s.subrange(0, s.len() as int) =~= s);
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
    /* code modified by LLM (iteration 5): Removed assume statements and fixed invariant initialization */
    let mut count: u8 = 0;
    let mut i: usize = 0;
    
    // Check for overflow before we start
    if s.len() > 255 {
        // If string is too long, we can't guarantee no overflow
        return 255;
    }
    
    proof {
        assert(i == 0);
        assert(s@.subrange(0, s@.len() as int) =~= s@);
        assert(count as int == 0);
        assert(count_vowels(s@) - count_vowels(s@) == 0);
    }
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count as int == count_vowels(s@.subrange(0, i as int)),
            count <= 255,
        decreases s.len() - i
    {
        if is_vowel_exec(s[i]) {
            if count == 255 {
                return 255;
            }
            count = count + 1;
        }
        
        proof {
            let old_i = i as int;
            assert(s@.subrange(0, old_i + 1) =~= s@.subrange(0, old_i) + seq![s@[old_i]]);
            if is_vowel(s@[old_i]) {
                assert(count_vowels(s@.subrange(0, old_i + 1)) == count_vowels(s@.subrange(0, old_i)) + 1);
            } else {
                assert(count_vowels(s@.subrange(0, old_i + 1)) == count_vowels(s@.subrange(0, old_i)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == s.len());
        assert(s@.subrange(0, i as int) =~= s@);
        lemma_count_from_index(s@, i as int);
    }
    
    if s.len() > 0 && s[s.len() - 1] == 'y' {
        if count == 255 {
            return 255;
        }
        count = count + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}