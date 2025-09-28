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
/* helper modified by LLM (iteration 5): Fixed lemma call syntax by using proof block */
proof fn lemma_concat_strings_empty()
    ensures concat_strings(Seq::<Seq<char>>::empty(), 0) == Seq::<char>::empty()
{
}

proof fn lemma_concat_strings_single(s: Seq<char>)
    ensures concat_strings(seq![s], 0) == s
{
}

proof fn lemma_concat_strings_step(strings: Seq<Seq<char>>, i: nat)
    requires i < strings.len()
    ensures concat_strings(strings, i) == strings[i as int] + concat_strings(strings, i + 1)
{
}

proof fn lemma_concat_strings_bounds(strings: Seq<Seq<char>>, i: nat)
    requires i >= strings.len()
    ensures concat_strings(strings, i) == Seq::<char>::empty()
{
}
// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed lemma call by using proof block */
{
    if strings.len() == 0 {
        proof {
            lemma_concat_strings_empty();
        }
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < strings.len()
        invariant
            0 <= i <= strings.len(),
            result@ == concat_strings(strings@.map(|k, s: Vec<char>| s@), 0).subrange(0, result@.len() as int)
    {
        let current_string = &strings[i];
        
        let mut j = 0;
        while j < current_string.len()
            invariant
                0 <= j <= current_string.len()
        {
            result.push(current_string[j]);
            j += 1;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}