// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed type casting and indexing with proper ghost/native separation */
fn string_to_seq(s: &String) -> Seq<char> {
    s.chars().collect()
}

/* helper modified by LLM (iteration 5): Fixed type conversions and indexing with proper ghost/native separation */
fn pad_left(s: String, target_width: usize, fillchar: char) -> (result: String)
    ensures
        result@.len() >= s@.len(),
        result@.len() == target_width as nat,
        forall|i: int| 0 <= i < s@.len() ==> result@[i + (target_width as int - s@.len())] == s@[i],
        forall|i: int| 0 <= i < target_width as int - s@.len() ==> result@[i] == fillchar
{
    let s_seq = string_to_seq(&s);
    let mut result = String::new();
    let padding_needed = target_width - s_seq.len();
    let mut i: usize = 0;
    while i < padding_needed
        invariant
            i <= padding_needed,
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == fillchar
    {
        result.push(fillchar);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < s_seq.len()
        invariant
            j <= s_seq.len(),
            result@.len() == padding_needed + j as nat,
            forall|k: int| 0 <= k < padding_needed as int ==> result@[k] == fillchar,
            forall|k: int| 0 <= k < j as int ==> result@[padding_needed as int + k] == s_seq[k]
    {
        result.push(s_seq[j as int]);
        j = j + 1;
    }
    result
}

proof fn pad_left_lemma(s: Seq<char>, target_width: int, fillchar: char)
    requires
        s.len() <= target_width,
    ensures
        pad_left(String::from_iter(s), target_width as usize, fillchar)@.len() == target_width,
        forall|i: int| 0 <= i < s.len() ==> pad_left(String::from_iter(s), target_width as usize, fillchar)@[i + (target_width - s.len())] == s[i],
        forall|i: int| 0 <= i < target_width - s.len() ==> pad_left(String::from_iter(s), target_width as usize, fillchar)@[i] == fillchar
{
}
// </vc-helpers>

// <vc-spec>
fn center(a: Vec<String>, width: Vec<usize>, fillchar: char) -> (result: Vec<String>)
    requires 
        a.len() == width.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i]@.len() >= 0 && {
                let orig_len = a[i]@.len() as int;
                let target_width = width[i] as int;
                &&& (orig_len >= target_width ==> result[i] == a[i])
                &&& result[i]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
            }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type conversions and loop invariants with proper ghost/native separation */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let orig_len = a[j]@.len() as int;
                let target_width = width[j] as int;
                &&& result[j]@.len() as int == if orig_len >= target_width { orig_len } else { target_width }
                &&& (orig_len >= target_width ==> result[j] == a[j])
            }
    {
        let orig_len = string_to_seq(&a[i]).len();
        let target_width = width[i];
        if orig_len >= target_width {
            result.push(a[i].clone());
        } else {
            let padded = pad_left(a[i].clone(), target_width, fillchar);
            result.push(padded);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}