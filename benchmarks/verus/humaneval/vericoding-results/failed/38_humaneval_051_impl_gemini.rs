// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_vowel(c: char) -> bool {
        c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u' || 
        c == 'A' || c == 'E' || c == 'I' || c == 'O' || c == 'U'
    }
    
spec fn valid_result(text: Seq<char>, result: Seq<char>) -> bool {
        && result.len() <= text.len()
        && (forall|i: int| 0 <= i < result.len() ==> !is_vowel(result[i]))
        && (forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i < j < result.len() ==> 
            (exists|k: int, l: int| 0 <= k < l < text.len() && text[k] == result[i] && text[l] == result[j] &&
            !is_vowel(text[k]) && !is_vowel(text[l])))
        && ((forall|i: int| 0 <= i < text.len() ==> is_vowel(text[i])) ==> result.len() == 0)
        && (forall|i: int| 0 <= i < text.len() && !is_vowel(text[i]) ==> result.contains(text[i]))
        && (forall|c: char| result.contains(c) ==> text.contains(c) && !is_vowel(c))
    }
    
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [use correct lemma names from vstd::seq_lib and logic for subsequence property] */
proof fn lemma_filter_implies_valid_result(text: Seq<char>, result: Seq<char>)
    requires
        result == text.filter(|c: char| !is_vowel(c)),
    ensures
        valid_result(text, result),
{
    let p = |c: char| !is_vowel(c);

    vstd::seq_lib::lemma_filter_len(text, p);
    
    vstd::seq_lib::lemma_filter_is_subsequence(text, p);
    assert forall |i: int, j: int| 0 <= i < j < result.len() implies
        (exists|k: int, l: int| 0 <= k < l < text.len() && text[k] == result[i] && text[l] == result[j] &&
            !is_vowel(text[k]) && !is_vowel(text[l]))
    by {
        let f = choose |f: spec_fn(int) -> int| {
            (forall|idx: int| 0 <= idx < result.len() ==> 0 <= f(idx) < text.len() && text[f(idx)] == result[idx]) &&
            (forall|idx1: int, idx2: int| 0 <= idx1 < idx2 < result.len() ==> f(idx1) < f(idx2))
        };
        let k = f(i);
        let l = f(j);
        
        assert(p(result[i]));
        assert(!is_vowel(text[k]));
        
        assert(p(result[j]));
        assert(!is_vowel(text[l]));
    };

    if forall|i: int| 0 <= i < text.len() ==> is_vowel(text[i]) {
        assert forall |c: char| text.contains(c) implies !p(c) by {
            let i = text.index_of(c);
            assert(is_vowel(text[i]));
        }
        vstd::seq_lib::lemma_filter_empty_if_all_fails(text, p);
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_vowels(text: &str) -> (result: String)
    ensures valid_result(text@, result@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): [use correct lemma from vstd::seq_lib and fix loop invariant proof] */
    let text_seq = text@;
    let p = |c: char| !is_vowel(c);

    let chars: Vec<char> = text.chars().collect();
    assert(chars@ === text_seq);

    let mut result_str = String::new();
    let mut i: usize = 0;
    while i < chars.len()
        invariant
            text@ === text_seq,
            chars@ === text_seq,
            0 <= i <= chars.len(),
            p === (|c: char| !is_vowel(c)),
            result_str@ === text_seq.subseq(0, i as int).filter(p),
    {
        let c = chars[i];
        
        proof {
            let s_i = text_seq.subseq(0, i as int);
            vstd::seq_lib::lemma_filter_push(s_i, c, p);
        }

        if !is_vowel(c) {
            result_str.push(c);
        }
        i = i + 1;
    }

    proof {
        let result_seq = result_str@;
        assert(i == text_seq.len());
        assert(result_seq === text_seq.subseq(0, text_seq.len() as int).filter(p));
        assert(text_seq.subseq(0, text_seq.len() as int) === text_seq);
        assert(result_seq === text_seq.filter(p));
        lemma_filter_implies_valid_result(text_seq, result_seq);
    }

    result_str
}
// </vc-code>


}

fn main() {}