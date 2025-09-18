// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed syntax error in split_once and added proper termination for find */
fn split_once(s: String, sep: String) -> (Option<(String, String)>, bool)
    ensures
        result.1 ==> (
            match result.0 {
                Some((before, after)) => before@ + sep@ + after@ == s@,
                None => s@.len() > 0
            }
        )
{
    if s@.contains(sep@) {
        let idx = s@.find(sep@).value() as nat;
        let before = s@.subrange(0, idx).to_string();
        let after = s@.subrange(idx + sep@.len(), s@.len()).to_string();
        (Some((before, after)), true)
    } else {
        (None, true)
    }
}

proof fn helper_lemma(s: String, sep: String)
    ensures
        match split_once(s, sep).0 {
            Some((before, after)) => before@ + sep@ + after@ == s@,
            None => true
        }
{
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
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
/* code modified by LLM (iteration 5): Fixed invariant syntax by adding parentheses */
{
    let mut before_vec = Vec::new();
    let mut sep_vec = Vec::new();
    let mut after_vec = Vec::new();
    let s = a.len();
    
    let mut i = 0;
    while i < s
        invariant (
            before_vec.len() == i && 
            sep_vec.len() == i && 
            after_vec.len() == i
        )
        decreases s - i;
    {
        let current = a[i].clone();
        let (split_result, found) = split_once(current, sep.clone());
        
        match split_result {
            Some((before, after)) => {
                before_vec.push(before);
                sep_vec.push(sep.clone());
                after_vec.push(after);
            },
            None => {
                before_vec.push(current.clone());
                sep_vec.push(String::new());
                after_vec.push(String::new());
            }
        }
        i += 1;
    }
    
    (before_vec, sep_vec, after_vec)
}
// </vc-code>

}
fn main() {}