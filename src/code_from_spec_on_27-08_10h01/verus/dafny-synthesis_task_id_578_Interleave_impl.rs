use vstd::prelude::*;

verus! {

// <vc-helpers>
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
{
    let mut result: Vec<int> = Vec::new();
    let mut i: nat = 0;
    
    while i < s1.len()
        invariant
            0 <= i <= s1.len(),
            result.len() == 3 * i,
            forall|j: int| 0 <= j < i ==> result@[3*j] == s1[j] && result@[3*j + 1] == s2[j] && result@[3*j + 2] == s3[j],
    {
        result.push(s1[i as int]);
        result.push(s2[i as int]);
        result.push(s3[i as int]);
        i += 1;
    }
    
    result@
}
// </vc-code>

fn main() {
}

}