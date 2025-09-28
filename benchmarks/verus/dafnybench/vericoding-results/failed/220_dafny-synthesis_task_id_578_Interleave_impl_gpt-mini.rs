use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let n: nat = s1.len();
    let mut v: Vec<int> = Vec::new();
    let mut i: nat = 0;
    while i < n
        invariant { i <= n }
        invariant { v.to_seq().len() == 3 * i }
        invariant { forall|j: nat| j < i ==> v.to_seq()@[(3 * j)] == s1@[j] && v.to_seq()@[(3 * j + 1)] == s2@[j] && v.to_seq()@[(3 * j + 2)] == s3@[j] }
        decreases { n - i }
    {
        v.push(s1@[i]);
        v.push(s2@[i]);
        v.push(s3@[i]);
        i = i + 1;
    }
    let r = v.to_seq();
    assert(r.len() == 3 * n);
    assert(forall|k: nat| k < n ==> r@[(3 * k)] == s1@[k] && r@[(3 * k + 1)] == s2@[k] && r@[(3 * k + 2)] == s3@[k]);
    r
}
// </vc-code>

fn main() {
}

}