// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [fixed compilation error using correct vstd lemmas and added decreases] */
fn partition_string(original: &String, sep: &String) -> (result: (String, String, String))
    ensures
        ({
            let (before, sep_part, after) = result;
            let original_seq = original@;
            let sep_seq = sep@;
            before@ + sep_part@ + after@ == original_seq &&
            (sep_part@ == sep_seq || sep_part@.len() == 0) &&
            (sep_part@.len() == 0 ==> after@.len() == 0 && before@ == original_seq) &&
            original_seq.len() == before@.len() + sep_part@.len() + after@.len()
        })
{
    if sep.len() == 0 {
        return (original.clone(), String::new(), String::new());
    }

    let mut i: usize = 0;
    while i + sep.len() <= original.len()
        invariant
            0 <= i <= original.len(),
            forall|j: int| 0 <= j < i ==> !(original@.subrange(j, j + sep@.len()) == sep@),
        decreases original.len() - i
    {
        let sub = original.substring_char(i, i + sep.len());
        if sub == *sep {
            let before_str = original.substring_char(0, i);
            let after_str = original.substring_char(i + sep.len(), original.len());
            
            assert(original@ == before_str@ + sub@ + after_str@) by {
                let s = original@;
                let i_int = i as int;
                let end1 = (i + sep.len()) as int;
                let end2 = original.len() as int;
                vstd::seq::lemma_subrange_join(s, i_int, end1, end2);
                vstd::seq::lemma_subrange_join(s, 0, i_int, end2);
            };

            return (before_str, sep.clone(), after_str);
        }
        i = i + 1;
    }

    (original.clone(), String::new(), String::new())
}

// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==> {
            let original = #[trigger] a[i]@;
            let before_i = result.0[i]@;
            let sep_i = result.1[i]@;
            let after_i = result.2[i]@;

            before_i + sep_i + after_i == original &&

            (sep_i == sep@ || sep_i.len() == 0) &&

            (sep_i.len() == 0 ==> after_i.len() == 0 && before_i == original) &&

            original.len() == before_i.len() + sep_i.len() + after_i.len()
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [calls helper function in a loop to process vector elements] */
{
    let mut befores: Vec<String> = Vec::new();
    let mut seps: Vec<String> = Vec::new();
    let mut afters: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            befores.len() == i,
            seps.len() == i,
            afters.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let original = a[j]@;
                let before_j = befores[j]@;
                let sep_j = seps[j]@;
                let after_j = afters[j]@;

                before_j + sep_j + after_j == original &&
                (sep_j == sep@ || sep_j.len() == 0) &&
                (sep_j.len() == 0 ==> after_j.len() == 0 && before_j == original) &&
                original.len() == before_j.len() + sep_j.len() + after_j.len()
            },
        decreases a.len() - i
    {
        let (before, sep_part, after) = partition_string(&a[i], &sep);
        befores.push(before);
        seps.push(sep_part);
        afters.push(after);
        i = i + 1;
    }
    (befores, seps, afters)
}

// </vc-code>

}
fn main() {}