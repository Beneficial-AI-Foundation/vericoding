// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn vec_string_to_seq(v: &Vec<String>) -> Seq<char> 
    ensures result == v@
{
    v@
}

proof fn string_ends_with_lemma(s: Seq<char>, suffix: Seq<char>) -> (b: bool)
    ensures b == string_ends_with(s, suffix)
{
    if suffix.len() > s.len() {
        false
    } else {
        s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
    }
}

/* helper modified by LLM (iteration 5): fixed return value in string_ends_with_lemma */
// </vc-helpers>

// <vc-spec>
spec fn string_ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    if suffix.len() > s.len() {
        false
    } else {
        s.subrange(s.len() - suffix.len(), s.len() as int) == suffix
    }
}

fn endswith(a: Vec<String>, suffix: Vec<String>) -> (result: Vec<bool>)
    requires a.len() == suffix.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            /* Main specification: result matches string_ends_with for each pair */
            result[i] == string_ends_with(a[i]@, suffix[i]@) &&
            /* Mathematical property: if result is true, suffix appears at the end */
            (result[i] ==> {
                suffix[i]@.len() <= a[i]@.len() &&
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) == suffix[i]@
            }) &&
            /* Mathematical property: if result is false, suffix does not appear at the end */
            (!result[i] ==> {
                suffix[i]@.len() > a[i]@.len() ||
                a[i]@.subrange(a[i]@.len() - suffix[i]@.len(), a[i]@.len() as int) != suffix[i]@
            })
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed result_vec return and subrange casting */
    let mut result_vec: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == string_ends_with(a[j]@, suffix[j]@)
    {
        let a_seq = a[i]@;
        let suffix_seq = suffix[i]@;
        
        proof {
            string_ends_with_lemma(a_seq, suffix_seq);
        }
        
        let ends = if suffix_seq.len() > a_seq.len() {
            false
        } else {
            a_seq.subrange(a_seq.len() - suffix_seq.len(), a_seq.len() as int) == suffix_seq
        };
        
        result_vec.push(ends);
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>


}
fn main() {}