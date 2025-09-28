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
/* helper modified by LLM (iteration 5): Unfolds one step of the `concat_strings` recursion. No code changes from previous correct helper. */
#[verifier(spinoff_prover)]
proof fn lemma_concat_unfold(strings: Seq<Seq<char>>, i: nat)
    requires
        i < strings.len(),
    ensures
        concat_strings(strings, i) == strings[i as int] + concat_strings(strings, i + 1),
{
    reveal_with_fuel(concat_strings, 2);
}
// </vc-helpers>

// <vc-spec>
fn concatenate(strings: Vec<Vec<char>>) -> (result: Vec<char>)
    ensures 
        result@ == concat_strings(strings@.map(|i, s: Vec<char>| s@), 0) &&
        (strings@.len() == 0 ==> result@ == Seq::<char>::empty())
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by using the correct sequence associativity lemma `vstd::seq_lib::lemma_seq_add_assoc`. */
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let s_map = strings@.map(|_, s: Vec<char>| s@);

    while i < strings.len()
        invariant
            i <= strings.len(),
            s_map == strings@.map(|_, s: Vec<char>| s@),
            concat_strings(s_map, 0) == result@ + concat_strings(s_map, i as nat),
        decreases strings.len() - i
    {
        proof {
            lemma_concat_unfold(s_map, i as nat);
        }

        let inner_vec = &strings[i];
        let mut j: usize = 0;
        let ghost result_at_iter_start = result@;

        while j < inner_vec.len()
            invariant
                i < strings.len(),
                j <= inner_vec.len(),
                s_map == strings@.map(|_, s: Vec<char>| s@),
                inner_vec@ == s_map[i as int],
                result@ == result_at_iter_start + inner_vec@.subrange(0, j as int),
            decreases inner_vec.len() - j
        {
            result.push(inner_vec[j]);
            j = j + 1;
        } 

        proof {
            vstd::seq_lib::lemma_seq_add_assoc(result_at_iter_start, inner_vec@, concat_strings(s_map, (i + 1) as nat));
        }

        i = i + 1;
    }

    result
}
// </vc-code>


}

fn main() {}