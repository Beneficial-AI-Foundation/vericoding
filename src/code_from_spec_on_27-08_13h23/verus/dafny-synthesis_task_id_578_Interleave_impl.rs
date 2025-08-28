use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers as the issue was a compilation error in the code section
// </vc-helpers>

// <vc-spec>
// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures 
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
#[verifier::exec_allows_no_decreases_clause]
fn interleave(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>) -> (r: Seq<int>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures 
        r.len() == 3 * s1.len(),
        forall|i: int| 0 <= i < s1.len() ==> r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
{
    let mut result: Vec<int> = Vec::new();
    let n = s1.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == 3 * i,
            forall|k: int| 0 <= k < i ==> result[3*k] == s1[k] && result[3*k + 1] == s2[k] && result[3*k + 2] == s3[k],
    {
        result.push(s1[i]);
        result.push(s2[i]);
        result.push(s3[i]);
        i = i + 1;
    }
    
    result.into_seq()
}
// </vc-code>

fn main() {
}

}