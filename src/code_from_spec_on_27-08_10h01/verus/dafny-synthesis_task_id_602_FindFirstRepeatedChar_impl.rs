use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn has_repeated_char_at_pos(s: Seq<char>, pos: int) -> bool {
    exists|j: int| pos < j < s.len() && s[pos] == s[j]
}

spec fn is_first_repeated_position(s: Seq<char>, pos: int) -> bool {
    has_repeated_char_at_pos(s, pos) && 
    (forall|i: int| 0 <= i < pos ==> !has_repeated_char_at_pos(s, i))
}

proof fn lemma_first_repeated_unique(s: Seq<char>, i: int, j: int)
    requires 
        0 <= i < j < s.len(),
        is_first_repeated_position(s, i),
        has_repeated_char_at_pos(s, j),
    ensures i <= j
{
    if i > j {
        assert(has_repeated_char_at_pos(s, j));
        assert(!has_repeated_char_at_pos(s, j));
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_first_repeated_char(s: &str) -> (result: (bool, char))
    ensures 
        (result.0 ==> exists|i: int, j: int| 0 <= i < j < s@.len() && s@[i] == s@[j] && s@[i] == result.1 && 
            (forall|k: int, l: int| 0 <= k < l < j && s@[k] == s@[l] ==> k >= i)) &&
        (!result.0 ==> (forall|i: int, j: int| 0 <= i < j < s@.len() ==> s@[i] != s@[j]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let chars = s@;
    let n = chars.len() as usize;
    
    for i in 0..n
        invariant
            forall|k: int, l: int| 0 <= k < l < i ==> chars[k] != chars[l]
    {
        for j in (i + 1)..n
            invariant
                0 <= i < n,
                i + 1 <= j <= n,
                forall|k: int, l: int| 0 <= k < l < i ==> chars[k] != chars[l],
                forall|l: int| i + 1 <= l < j ==> chars[i as int] != chars[l]
        {
            if chars[i as int] == chars[j as int] {
                proof {
                    let seq_chars = chars;
                    assert(seq_chars[i as int] == seq_chars[j as int]);
                    assert(0 <= i < j < seq_chars.len());
                    
                    assert(forall|k: int, l: int| 0 <= k < l < j && seq_chars[k] == seq_chars[l] ==> k >= i) by {
                        assert(forall|k: int, l: int| 0 <= k < l < i ==> seq_chars[k] != seq_chars[l]);
                        assert(forall|l: int| i + 1 <= l < j ==> seq_chars[i as int] != seq_chars[l]);
                    };
                }
                return (true, chars@[i as int]);
            }
        }
    }
    
    proof {
        assert(forall|i: int, j: int| 0 <= i < j < chars.len() ==> chars[i] != chars[j]);
    }
    
    (false, 'a')
}
// </vc-code>

fn main() {}

}