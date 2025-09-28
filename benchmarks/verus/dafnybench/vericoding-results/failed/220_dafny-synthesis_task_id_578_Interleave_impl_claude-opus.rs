use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper lemma to establish the postcondition for a partially constructed sequence
proof fn interleave_partial_correctness(s1: Seq<int>, s2: Seq<int>, s3: Seq<int>, r: Seq<int>, k: int)
    requires
        s1.len() == s2.len(),
        s2.len() == s3.len(),
        0 <= k <= s1.len(),
        r.len() == 3 * k,
        forall|i: int| 0 <= i < k ==> #[trigger] r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
    ensures
        forall|i: int| 0 <= i < k ==> #[trigger] r[3*i] == s1[i] && r[3*i + 1] == s2[i] && r[3*i + 2] == s3[i],
{
}
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
    let mut r: Seq<int> = seq![];
    let mut i: usize = 0;
    let n = s1.len();
    
    while i < n
        invariant
            i <= n,
            s1.len() == s2.len(),
            s2.len() == s3.len(),
            s1.len() == n,
            r.len() == 3 * i,
            forall|j: int| 0 <= j < i ==> 
                #[trigger] r[3*j] == s1[j] && r[3*j + 1] == s2[j] && r[3*j + 2] == s3[j],
    {
        r = r.push(s1[i as int]);
        r = r.push(s2[i as int]);
        r = r.push(s3[i as int]);
        
        proof {
            assert(r.len() == 3 * (i as int) + 3);
            assert(r[3 * (i as int)] == s1[i as int]);
            assert(r[3 * (i as int) + 1] == s2[i as int]);
            assert(r[3 * (i as int) + 2] == s3[i as int]);
            
            // Preserve the invariant for previous iterations
            assert forall|j: int| 0 <= j < i ==> 
                #[trigger] r[3*j] == s1[j] && r[3*j + 1] == s2[j] && r[3*j + 2] == s3[j]
            by {
                // Previous elements remain unchanged by push operations
            }
        }
        
        i = i + 1;
    }
    
    r
}
// </vc-code>

fn main() {
}

}