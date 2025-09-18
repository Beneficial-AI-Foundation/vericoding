// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed uninterpreted function warning, type errors, and indexing issues */
spec#[uninterp] fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool;

exec fn compare_strings(s1: &String, s2: &String) -> bool {
    let mut chars1 = s1.chars();
    let mut chars2 = s2.chars();
    loop {
        match (chars1.next(), chars2.next()) {
            (Some(c1), Some(c2)) => {
                if c1 > c2 {
                    return true;
                } else if c1 < c2 {
                    return false;
                }
            }
            (Some(_), None) => return true,
            (None, Some(_)) => return false,
            (None, None) => return false,
        }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool;

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed indexing and type mismatches in invariant */
    let mut result = Vec::with_capacity(x1.len());
    for i in 0..x1.len()
        invariant 
            0 <= (i as int) <= x1.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> 
                result[j as usize] == string_compare_gt(x1[j]@, x2[j]@),
            forall|j: int| 0 <= j < (i as int) ==> 
                result[j as usize] ==> !string_compare_gt(x2[j]@, x1[j]@),
            forall|j: int| 0 <= j < (i as int) ==> 
                (x1[j]@ == x2[j]@) ==> (result[j as usize] == false)
    {
        let s1 = &x1[i];
        let s2 = &x2[i];
        let cmp = compare_strings(s1, s2);
        result.push(cmp);
    }
    result
}
// </vc-code>

}
fn main() {}