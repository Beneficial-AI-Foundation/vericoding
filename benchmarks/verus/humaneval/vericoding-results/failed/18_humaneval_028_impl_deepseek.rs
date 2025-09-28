// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn concat_strings(strings: Seq<Seq<char>>, index: nat) -> Seq<char>
    decreases strings.len() - index
{
    if index >= strings.len() {
        Seq::<char>::empty()
    } else {
        strings[index as int] + concat_strings(strings, index + 1)
    }
}
// </vc-preamble>

// <vc-helpers>

proof fn seq_concat_proof(s: Seq<Seq<char>>, i: nat)
    requires i < s.len()
    ensures concat_strings(s, i) == s[i as int] + concat_strings(s, i + 1)
    decreases s.len() - i
{
    reveal(concat_strings);
}

proof fn string_concat_lemma(s: Seq<Seq<char>>, i: nat, j: nat)
    requires i <= j <= s.len()
    ensures concat_strings(s, i) == concat_strings(s.subrange(i as int, j as int), 0) + concat_strings(s, j)
    decreases j - i
{
    if i < j {
        seq_concat_proof(s, i);
        assert(concat_strings(s.subrange(i as int, j as int), 0) == s[i as int] + concat_strings(s.subrange(i as int + 1, j as int), 0));
        string_concat_lemma(s, i + 1, j);
        assert(concat_strings(s, i) == s[i as int] + concat_strings(s, i + 1));
    } else {
        assert(i == j);
    }
}

/* helper modified by LLM (iteration 5): Enhanced string_concat_lemma with proper subrange reasoning and calls to seq_concat_proof */
// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Complete rewrite with proper initialization and loop invariants */
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings@.len(),
            result@ == concat_strings(strings@.map(|idx, s: Vec<char>| s@), i as nat),
        decreases strings@.len() - i
    {
        let current_string = &strings[i];
        let mut j: usize = 0;
        
        while j < current_string.len()
            invariant
                0 <= j <= current_string@.len(),
                result@ == concat_strings(strings@.map(|idx, s: Vec<char>| s@), i as nat) + current_string@.subrange(0, j as int),
            decreases current_string@.len() - j
        {
            result.push(current_string[j]);
            j = j + 1;
        }
        
        proof {
            seq_concat_proof(strings@.map(|idx, s: Vec<char>| s@), i as nat);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}