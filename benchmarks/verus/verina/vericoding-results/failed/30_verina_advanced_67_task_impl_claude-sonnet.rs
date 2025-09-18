// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed lambda pattern syntax by using explicit variable */
spec fn decode_rle_impl(lst: Vec<(char, usize)>) -> Seq<char>
    decreases lst.len()
{
    if lst.len() == 0 {
        Seq::empty()
    } else {
        let first = lst[0];
        let rest = lst@.subrange(1, lst.len() as int);
        Seq::new(first.1 as nat, |i: int| first.0) + decode_rle_seq(rest)
    }
}

spec fn decode_rle_seq(lst: Seq<(char, usize)>) -> Seq<char>
    decreases lst.len()
{
    if lst.len() == 0 {
        Seq::empty()
    } else {
        let first = lst[0];
        let rest = lst.subrange(1, lst.len() as int);
        Seq::new(first.1 as nat, |i: int| first.0) + decode_rle_seq(rest)
    }
}

proof fn decode_rle_equivalence(lst: Vec<(char, usize)>)
    ensures decode_rle(lst) == decode_rle_impl(lst)
{
}

proof fn decode_rle_append_lemma(a: Vec<(char, usize)>, b: Vec<(char, usize)>)
    ensures decode_rle_seq(a@ + b@) == decode_rle_impl(a) + decode_rle_impl(b)
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        let rest_a = a@.subrange(1, a.len() as int);
        decode_rle_append_lemma_seq(rest_a, b@);
    }
}

proof fn decode_rle_append_lemma_seq(a: Seq<(char, usize)>, b: Seq<(char, usize)>)
    ensures decode_rle_seq(a + b) == decode_rle_seq(a) + decode_rle_seq(b)
    decreases a.len()
{
    if a.len() == 0 {
    } else {
        let rest_a = a.subrange(1, a.len() as int);
        decode_rle_append_lemma_seq(rest_a, b);
    }
}
// </vc-helpers>

// <vc-spec>
fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clause to while loop */
    let mut result: Vec<(char, usize)> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| 0 <= j < result.len() ==> result[j].1 > 0,
            forall|j: int| 0 <= j < result.len() ==> j + 1 < result.len() ==> result[j].0 != result[j + 1].0,
        decreases s.len() - i
    {
        let current_char = s[i];
        let mut count: usize = 1;
        
        while i + count < s.len() && s[i + count] == current_char
            invariant
                0 <= i < s.len(),
                count >= 1,
                i + count <= s.len(),
                forall|k: int| i <= k < i + count ==> s[k as int] == current_char,
            decreases s.len() - (i + count)
        {
            count += 1;
        }
        
        result.push((current_char, count));
        i += count;
    }
    
    result
}
// </vc-code>

}
fn main() {}