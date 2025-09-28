// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed to proper Verus predicate syntax */
predicate starts_with(s: Seq<char>, prefix: Seq<char>) -> bool {
    prefix.len() > 0 ==> (s.len() >= prefix.len() && 
    forall|i: int| 0 <= i < prefix.len() ==> s[i] == prefix[i])
}

spec fn find_first_occurrence(s: Seq<char>, sep: Seq<char>) -> (idx: int)
    recommends sep.len() > 0
    ensures
        -1 <= idx <= s.len(),
        idx == -1 ==> !starts_with(s, sep) && forall|j| 0 <= j <= s.len() - sep.len() ==> !starts_with(s.drop(j), sep),
        idx >= 0 ==> idx <= s.len() - sep.len() && starts_with(s.drop(idx), sep) && 
                     forall|j| 0 <= j < idx ==> !starts_with(s.drop(j), sep)
{
    if s.len() < sep.len() {
        -1
    } else {
        let mut i: int = 0;
        while i <= s.len() - sep.len()
            invariant
                i <= s.len() - sep.len() + 1,
                forall|j: int| 0 <= j < i ==> !starts_with(s.drop(j), sep)
            decreases s.len() - i - sep.len() + 1
        {
            if starts_with(s.drop(i), sep) {
                return i;
            }
            i = i + 1;
        }
        -1
    }
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
{
    /* code modified by LLM (iteration 5): Fixed sequence operations, type conversions and proper return */
    let mut before_vec = Vec::new();
    let mut sep_vec = Vec::new();
    let mut after_vec = Vec::new();
    
    let mut i = 0;
    while i < a.len()
        invariant
            before_vec@.len() == i as nat,
            sep_vec@.len() == i as nat,
            after_vec@.len() == i as nat,
            forall|j: int| 0 <= j < i ==> {
                let original = a@[j as int]@;
                let before_part = before_vec@[j as int]@;
                let sep_part = sep_vec@[j as int]@;
                let after_part = after_vec@[j as int]@;
                
                before_part + sep_part + after_part == original &&
                (sep_part == sep@ || sep_part.len() == 0) &&
                (sep_part.len() == 0 ==> after_part.len() == 0 && before_part == original) &&
                original.len() == before_part.len() + sep_part.len() + after_part.len()
            }
        decreases a.len() - i
    {
        let original_str = &a[i];
        let original_seq = original_str@;
        let sep_seq = sep@;
        
        let idx = if sep_seq.len() > 0 { find_first_occurrence(original_seq, sep_seq) } else { -1 };
        
        if sep_seq.len() == 0 {
            before_vec.push(original_str.clone());
            sep_vec.push(String::new());
            after_vec.push(String::new());
        } else if idx >= 0 && idx <= (original_seq.len() as int - sep_seq.len() as int) {
            let before_chars = original_seq.subrange(0, idx as usize);
            let sep_chars = original_seq.subrange(idx as usize, idx as usize + sep_seq.len());
            let after_chars = original_seq.subrange(idx as usize + sep_seq.len(), original_seq.len());
            
            before_vec.push(String::from_chars(before_chars));
            sep_vec.push(String::from_chars(sep_chars));
            after_vec.push(String::from_chars(after_chars));
        } else {
            before_vec.push(original_str.clone());
            sep_vec.push(String::new());
            after_vec.push(String::new());
        }
        
        i = i + 1;
    }
    
    (before_vec, sep_vec, after_vec)
}
// </vc-code>

}
fn main() {}