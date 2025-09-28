// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed ghost type usage in executable code */
proof fn lemma_all_chars_alpha_implies_each(s: Seq<char>, j: int)
    requires
        0 <= j < s.len(),
        all_chars_alpha(s)
    ensures
        is_alpha_char(s[j])
    decreases s.len(), j
{
    if j == 0 {
        assert(s[0] == s[0]);
    } else {
        lemma_all_chars_alpha_implies_each(s.skip(1), j - 1);
        assert(s[j] == s.skip(1)[j - 1]);
    }
}

fn check_all_alpha(s: &String) -> (result: bool)
    ensures
        result == (s@.len() > 0 && all_chars_alpha(s@))
{
    let len = s.len();
    
    if len == 0 {
        return false;
    }
    
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == s@.len(),
            forall|j: int| 0 <= j < i ==> is_alpha_char(s@[j])
    {
        let c = s.get_char(i);
        if !((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) {
            proof {
                assert(!is_alpha_char(c));
                assert(c == s@[i as int]);
                assert(!all_chars_alpha(s@));
            }
            return false;
        }
        i = i + 1;
    }
    
    proof {
        assert(i == s@.len());
        assert forall|j: int| 0 <= j < s@.len() implies is_alpha_char(s@[j]) by {
            assert(is_alpha_char(s@[j]));
        }
        assert(all_chars_alpha(s@)) by {
            let mut k: int = s@.len() as int;
            while k > 0
                invariant
                    0 <= k <= s@.len(),
                    all_chars_alpha(s@.skip(k))
            {
                k = k - 1;
                assert(is_alpha_char(s@[k]));
                assert(s@.skip(k)[0] == s@[k]);
                assert(s@.skip(k).skip(1) =~= s@.skip(k + 1));
            }
            assert(s@.skip(0) =~= s@);
        }
    }
    true
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): No changes needed in main code */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (a[j]@.len() > 0 && all_chars_alpha(a[j]@))
    {
        let is_alpha = check_all_alpha(&a[i]);
        result.push(is_alpha);
        i = i + 1;
    }
    
    assert(result.len() == a.len());
    assert forall|i: int| 0 <= i < a.len() implies
        result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)) by {
        assert(result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)));
    }
    
    result
}
// </vc-code>


}
fn main() {}