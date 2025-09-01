use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> (ret:bool) {
    c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || c == 'A' || c == 'E' || c == 'I'
        || c == 'O' || c == 'U'
}
// pure-end
// pure-end

spec fn vowels(s: Seq<char>) -> (ret:Seq<char>) {
    s.filter(|c| is_vowel(c))
}
// pure-end
// pure-end

spec fn inner_expr_vowels_count(s: &str, ret: u32) -> (ret:bool) {
    ret == vowels(s@).len() + if (s@.len() > 0 && (s@.last() == 'y' || s@.last() == 'Y')) {
        1int

    } else {
        0int
    }
}
// pure-end

// <vc-helpers>
proof fn filter_len_bound(s: Seq<char>)
    ensures
        vowels(s).len() <= s.len(),
{
    // The filter operation always produces a sequence with length <= original
    // This is a fundamental property that Verus should recognize
    assert(s.filter(|c| is_vowel(c)).len() <= s.len());
}

proof fn vowels_push(s: Seq<char>, c: char)
    ensures
        vowels(s.push(c)) == if is_vowel(c) {
            vowels(s).push(c)
        } else {
            vowels(s)
        },
{
    assert(s.push(c).filter(|x| is_vowel(x)) == if is_vowel(c) {
        s.filter(|x| is_vowel(x)).push(c)
    } else {
        s.filter(|x| is_vowel(x))
    });
}

proof fn vowels_subrange(s: Seq<char>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
    ensures
        vowels(s.subrange(i, j)).len() <= j - i,
{
    filter_len_bound(s.subrange(i, j));
    assert(s.subrange(i, j).len() == j - i);
}
// </vc-helpers>

// <vc-spec>
fn vowels_count(s: &str) -> (ret: u32)
    // pre-conditions-start
    requires
        s@.len() <= u32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        inner_expr_vowels_count(s, ret),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut count: u32 = 0;
    let mut i: usize = 0;
    
    while i < s.unicode_len()
        invariant
            i <= s.unicode_len(),
            count <= i,
            count == vowels(s@.subrange(0, i as int)).len(),
            s@.len() <= u32::MAX,
    {
        let c = s.get_char(i);
        
        proof {
            vowels_subrange(s@, 0, i as int);
            assert(vowels(s@.subrange(0, i as int)).len() <= i);
        }
        
        if is_vowel(c) {
            proof {
                assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
                vowels_push(s@.subrange(0, i as int), c);
                assert(c == s@[i as int]);
                assert(is_vowel(s@[i as int]));
                assert(vowels(s@.subrange(0, (i + 1) as int)) == vowels(s@.subrange(0, i as int)).push(c));
                assert(vowels(s@.subrange(0, (i + 1) as int)).len() == vowels(s@.subrange(0, i as int)).len() + 1);
            }
            count = count + 1;
        } else {
            proof {
                assert(s@.subrange(0, (i + 1) as int) == s@.subrange(0, i as int).push(s@[i as int]));
                vowels_push(s@.subrange(0, i as int), c);
                assert(c == s@[i as int]);
                assert(!is_vowel(s@[i as int]));
                assert(vowels(s@.subrange(0, (i + 1) as int)) == vowels(s@.subrange(0, i as int)));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(s@.subrange(0, s@.len() as int) == s@);
    }
    
    if s.unicode_len() > 0 {
        let last_char = s.get_char(s.unicode_len() - 1);
        if last_char == 'y' || last_char == 'Y' {
            proof {
                assert(s@[s@.len() - 1] == last_char);
                assert(s@.last() == s@[s@.len() - 1]);
            }
            count = count + 1;
        }
    }
    
    count
}
// </vc-code>

fn main() {}
}