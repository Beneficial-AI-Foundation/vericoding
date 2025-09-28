use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n: usize = s1.len() as usize;
    let mut v: Vec<int> = Vec::with_capacity(3 * n);
    for i in 0..n
        invariant
            v.len() == 3 * i,
            forall|j: int| 0 <= j < i ==> {
                &&& #[trigger] v@[(3*j) as usize] == s1[j]
                &&& #[trigger] v@[(3*j + 1) as usize] == s2[j]
                &&& #[trigger] v@[(3*j + 2) as usize] == s3[j]
            }
    {
        v.push(s1[i]);
        v.push(s2[i]);
        v.push(s3[i]);
    }
    let r = v.view();
    assert(r.len() == 3 * n as int);
    assert forall|i: int| 0 <= i < n as int implies r[3*i] == s1[i] by {
        assert(0 <= i < n as int);
        assert(v@[(3*i) as usize] == s1[i]);
        assert(r[3*i] == v@[(3*i) as usize]);
    }
    assert forall|i: int| 0 <= i < n as int implies r[3*i + 1] == s2[i] by {
        assert(0 <= i < n as int);
        assert(v@[(3*i + 1) as usize] == s2[i]);
        assert(r[3*i + 1] == v@[(3*i + 1) as usize]);
    }
    assert forall|i: int| 0 <= i < n as int implies r[3*i + 2] == s3[i] by {
        assert(0 <= i < n as int);
        assert(v@[(3*i + 2) as usize] == s3[i]);
        assert(r[3*i + 2] == v@[(3*i + 2) as usize]);
    }
    r
}
// </vc-code>

fn main() {
}

}