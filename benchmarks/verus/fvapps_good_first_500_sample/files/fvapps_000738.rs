// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn vowels() -> Set<char> {
    set!['A', 'E', 'I', 'O', 'U']
}

spec fn is_vowel(c: char) -> bool {
    vowels().contains(c)
}

spec fn is_uppercase_char(c: char) -> bool {
    c >= 'A' && c <= 'Z'
}

spec fn has_adjacent_vowels(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() < 2 {
        false
    } else {
        (is_vowel(s[0]) && is_vowel(s[1])) || has_adjacent_vowels(s.skip(1))
    }
}

spec fn rotate_string(s: Seq<char>, i: nat) -> Seq<char> {
    if i >= s.len() {
        s
    } else {
        s.subrange(i as int, s.len() as int) + s.subrange(0, i as int)
    }
}

spec fn exists_clingy_rotation(s: Seq<char>) -> bool {
    exists|i: nat| i < s.len() && has_adjacent_vowels(rotate_string(s, i))
}

spec fn all_uppercase(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_uppercase_char(s[i])
}

spec fn all_vowels(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_vowel(s[i])
}

spec fn all_consonants(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> !is_vowel(s[i])
}
// </vc-helpers>

// <vc-spec>
fn is_clingy(s: Vec<char>) -> (result: bool)
    requires all_uppercase(s@),
    ensures 
        result <==> exists_clingy_rotation(s@),
        all_vowels(s@) && s@.len() >= 2 ==> result == true,
        all_consonants(s@) ==> result == false,
        s@.len() == 1 ==> result == false
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


/* Apps difficulty: interview */
/* Assurance level: unguarded */

/*
fn test_is_clingy() {
    assert(is_clingy(vec!['A', 'U', 'X', 'F', 'C']));
    assert(!is_clingy(vec!['X', 'B', 'C', 'D', 'E', 'F']));
    assert(is_clingy(vec!['A', 'E', 'I', 'O', 'U']));
}
*/

}

fn main() {
    // test_is_clingy();
}