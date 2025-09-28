// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn has_letter(s: Seq<char>) -> bool
{
    exists|i: int| 0 <= i < s.len() && (('A' <= s[i] && s[i] <= 'Z') || ('a' <= s[i] && s[i] <= 'z'))
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 { 
        s 
    } else { 
        s.subrange(s.len() as int - 1, s.len() as int).add(reverse_string(s.subrange(0, s.len() as int - 1)))
    }
}

spec fn swap_case(c: char) -> char
{
    if 'A' <= c && c <= 'Z' { 
        ((c as u32 + 32) as char)
    } else if 'a' <= c && c <= 'z' { 
        ((c as u32 - 32) as char)
    } else { 
        c 
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove iterative reversal equals recursive spec */
proof fn lemma_reverse_string_iterative(s: Seq<char>, result: Seq<char>)
    requires
        result.len() == s.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == s[s.len() - 1 - i]
    ensures
        result == reverse_string(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(result == s);
    } else {
        let last = s.subrange(s.len() - 1, s.len());
        let rest = s.subrange(0, s.len() - 1);
        let result_rest = result.subrange(1, result.len());
        
        assert(result[0] == s[s.len() - 1]);
        assert(last.len() == 1);
        assert(last[0] == s[s.len() - 1]);
        assert(result[0] == last[0]);
        
        assert forall|i: int| 0 <= i < result_rest.len() implies result_rest[i] == rest[rest.len() - 1 - i] by {
            let i_in_result = i + 1;
            assert(result_rest[i] == result[i_in_result]);
            assert(result[i_in_result] == s[s.len() - 1 - i_in_result]);
            assert(s[s.len() - 1 - i_in_result] == rest[rest.len() - 1 - i]);
        }
        
        lemma_reverse_string_iterative(rest, result_rest);
        assert(result_rest == reverse_string(rest));
        assert(result == last.add(result_rest));
        assert(reverse_string(s) == last.add(reverse_string(rest)));
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    ensures (if has_letter(s@) {
        result@.len() == s@.len() && 
        (forall|i: int| 0 <= i < s@.len() ==> result@[i] == swap_case(s@[i]))
    } else {
        result@ == reverse_string(s@)
    }) && result@.len() == s@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added call to helper lemma to prove reverse equivalence */
    let mut has_letter_flag = false;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            has_letter_flag == exists|j: int| 0 <= j < i && (('A' <= s@[j] && s@[j] <= 'Z') || ('a' <= s@[j] && s@[j] <= 'z'))
        decreases s.len() - i
    {
        let c = s[i];
        if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') {
            has_letter_flag = true;
        }
        i = i + 1;
    }
    
    assert(has_letter_flag == has_letter(s@));
    
    if has_letter_flag {
        let mut result = Vec::new();
        let mut j: usize = 0;
        while j < s.len()
            invariant
                0 <= j <= s.len(),
                result@.len() == j,
                forall|k: int| 0 <= k < j ==> result@[k] == swap_case(s@[k])
            decreases s.len() - j
        {
            let c = s[j];
            let swapped = if 'A' <= c && c <= 'Z' {
                // Convert uppercase to lowercase
                let offset = (c as u8) - ('A' as u8);
                (('a' as u8) + offset) as char
            } else if 'a' <= c && c <= 'z' {
                // Convert lowercase to uppercase
                let offset = (c as u8) - ('a' as u8);
                (('A' as u8) + offset) as char
            } else {
                c
            };
            result.push(swapped);
            j = j + 1;
        }
        result
    } else {
        let mut result = Vec::new();
        let mut k: usize = s.len();
        while k > 0
            invariant
                0 <= k <= s.len(),
                result@.len() == s.len() - k,
                forall|idx: int| 0 <= idx < result@.len() ==> result@[idx] == s@[s.len() - 1 - idx]
            decreases k
        {
            k = k - 1;
            result.push(s[k]);
        }
        proof {
            lemma_reverse_string_iterative(s@, result@);
        }
        result
    }
}
// </vc-code>


}

fn main() {}