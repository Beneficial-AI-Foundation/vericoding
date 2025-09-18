// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define lexicographic greater for sequences and prove irreflexivity and asymmetry */
open spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        false
    } else if s2.len() == 0 {
        true
    } else if s1[0] == s2[0] {
        string_compare_gt(s1.drop(1), s2.drop(1))
    } else {
        s1[0] > s2[0]
    }
}

/* helper modified by LLM (iteration 5): proof by structural induction on the sequence for irreflexivity */
proof fn lemma_string_compare_irreflexive(s: Seq<char>)
    ensures !string_compare_gt(s, s)
    decreases s.len()
{
    if s.len() == 0 {
        // string_compare_gt([], []) == false by definition
    } else {
        assert(s[0] == s[0]);
        lemma_string_compare_irreflexive(s.drop(1));
    }
}

/* helper modified by LLM (iteration 5): proof by case analysis and induction for asymmetry */
proof fn lemma_string_compare_asym(s1: Seq<char>, s2: Seq<char>)
    ensures string_compare_gt(s1, s2) ==> !string_compare_gt(s2, s1)
    decreases s1.len() + s2.len()
{
    if s1.len() == 0 {
        // Antecedent false
    } else if s2.len() == 0 {
        // Then string_compare_gt(s1, []) is true and string_compare_gt([], s1) is false
    } else if s1[0] == s2[0] {
        lemma_string_compare_asym(s1.drop(1), s2.drop(1));
    } else {
        // Heads differ: if s1[0] > s2[0], then !(s2[0] > s1[0]);
        // Hence string_compare_gt(s2, s1) is false when the antecedent holds.
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
    /* code modified by LLM (iteration 5): build result via loop and use proven lexicographic properties; fix int/usize indexing in proofs */
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result[j] == string_compare_gt(x1[j]@, x2[j]@),
            forall|j: int| 0 <= j && j < i as int ==> result[j] ==> !string_compare_gt(x2[j]@, x1[j]@),
            forall|j: int| 0 <= j && j < i as int ==> (x1[j]@ == x2[j]@) ==> (result[j] == false)
    {
        let ii: int = i as int;
        let b: bool = string_compare_gt(x1[ii]@, x2[ii]@);
        result.push(b);
        proof {
            assert(result[ii] == b);
            if result[ii] {
                lemma_string_compare_asym(x1[ii]@, x2[ii]@);
            }
            if x1[ii]@ == x2[ii]@ {
                lemma_string_compare_irreflexive(x1[ii]@);
                assert(b == string_compare_gt(x1[ii]@, x2[ii]@));
                assert(b == false);
                assert(result[ii] == false);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}