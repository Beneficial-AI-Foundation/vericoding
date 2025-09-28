// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn filter_chars(s: Seq<char>, c: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else if c.contains(s[0]) {
        filter_chars(s.subrange(1, s.len() as int), c)
    } else {
        seq![s[0]].add(filter_chars(s.subrange(1, s.len() as int), c))
    }
}

spec fn reverse_seq(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        reverse_seq(s.subrange(1, s.len() as int)).add(seq![s[0]])
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof keyword to fix lemma syntax */
proof fn reverse_seq_involution(s: Seq<char>)
    ensures reverse_seq(reverse_seq(s)) == s
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        reverse_seq_involution(s.subrange(1, s.len() as int));
        assert(reverse_seq(s).last() == s[0]);
        assert(reverse_seq(s).subrange(0, reverse_seq(s).len() - 1) == reverse_seq(s.subrange(1, s.len() as int)));
    }
}

proof fn filter_chars_preserves_elements(s: Seq<char>, c: Seq<char>)
    ensures forall|i: int| #![auto] 0 <= i < filter_chars(s, c).len() ==> s.contains(filter_chars(s, c)[i])
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        filter_chars_preserves_elements(s.subrange(1, s.len() as int), c);
    }
}

proof fn filter_chars_excludes_chars(s: Seq<char>, c: Seq<char>)
    ensures forall|i: int| #![auto] 0 <= i < filter_chars(s, c).len() ==> !c.contains(filter_chars(s, c)[i])
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        filter_chars_excludes_chars(s.subrange(1, s.len() as int), c);
    }
}
// </vc-helpers>

// <vc-spec>
fn reverse_delete(s: Vec<char>, c: Vec<char>) -> (result: (Vec<char>, bool))
    ensures
        result.0@ == filter_chars(s@, c@),
        result.1 == (result.0@ == reverse_seq(result.0@)),
        result.0@.len() <= s@.len(),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> !c@.contains(result.0@[i]),
        forall|i: int| #![auto] 0 <= i < result.0@.len() ==> s@.contains(result.0@[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger inference for quantifier */
    let mut result: Vec<char> = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@ == filter_chars(s@.subrange(0, i as int), c@),
        decreases s.len() - i
    {
        let ch = s[i];
        let mut should_exclude = false;
        let mut j = 0;
        
        while j < c.len()
            invariant
                0 <= j <= c.len(),
                should_exclude == c@.subrange(0, j as int).contains(ch),
            decreases c.len() - j
        {
            if c[j] == ch {
                should_exclude = true;
            }
            j += 1;
        }
        
        if !should_exclude {
            result.push(ch);
        }
        i += 1;
    }
    
    proof {
        filter_chars_preserves_elements(s@, c@);
        filter_chars_excludes_chars(s@, c@);
    }
    
    let mut is_palindrome = true;
    let n = result.len();
    let mut k = 0;
    
    while k < n / 2
        invariant
            0 <= k <= n / 2,
            is_palindrome == (forall|idx: int| #![trigger result@[idx]] 0 <= idx < k ==> result@[idx] == result@[n - 1 - idx]),
        decreases n / 2 - k
    {
        if result[k] != result[n - 1 - k] {
            is_palindrome = false;
        }
        k += 1;
    }
    
    proof {
        if is_palindrome {
            assert(forall|idx: int| #![trigger result@[idx]] 0 <= idx < n ==> result@[idx] == result@[n - 1 - idx]);
            assert(result@ == reverse_seq(result@)) by {
                let rev = reverse_seq(result@);
                assert(rev.len() == result@.len());
                assert(forall|idx: int| #![trigger rev[idx]] 0 <= idx < n ==> rev[idx] == result@[n - 1 - idx]);
            }
        } else {
            assert(exists|idx: int| #![trigger result@[idx]] 0 <= idx < n && result@[idx] != result@[n - 1 - idx]);
            assert(result@ != reverse_seq(result@));
        }
    }
    
    (result, is_palindrome)
}
// </vc-code>


}

fn main() {}