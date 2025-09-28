// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures 
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation errors by using proof-mode logic and types */
    let mut r = Seq::<int>::empty();
    let mut i: nat = 0;
    while i < s1.len()
        invariant
            s1.len() == s2.len(),
            s2.len() == s3.len(),
            i <= s1.len(),
            r.len() == 3 * i,
            forall|j: nat| j < i ==> 
                r@[(3 * j) as int] == s1@[j as int] && 
                r@[(3 * j + 1) as int] == s2@[j as int] && 
                r@[(3 * j + 2) as int] == s3@[j as int],
        decreases s1.len() - i
    {
        let i_int = i as int;
        r = r.push(s1@[i_int]);
        r = r.push(s2@[i_int]);
        r = r.push(s3@[i_int]);
        i = i + 1;
    }
    r
}
// </vc-code>

}
fn main() {}