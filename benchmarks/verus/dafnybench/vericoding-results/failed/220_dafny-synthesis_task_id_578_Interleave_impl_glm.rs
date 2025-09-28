use vstd::prelude::*;

verus! {

// <vc-helpers>
ghost fn int_to_nat(i: int) -> (n: nat)
    ensures n as int == i,
{
    i as nat
}

ghost fn seq_len_nat<T>(s: Seq<T>) -> (n: nat)
    ensures n == s.len(),
{
    s.len()
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
    let n = s1.len();
    let mut r = Seq::new(3 * n, |i: int| 0);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            r.len() == 3 * n,
            forall|j: int| 0 <= j < i ==> 
                r[3*j] == s1[j] && r[3*j+1] == s2[j] && r[3*j+2] == s3[j],
    {
        r = r.update(3*i, s1[i]);
        r = r.update(3*i+1, s2[i]);
        r = r.update(3*i+2, s3[i]);
        i = i + 1;
        proof {
            assert forall|k: int| 0 <= k < i implies #[trigger] r[3*k] == s1[k] && r[3*k+1] == s2[k] && r[3*k+2] == s3[k] by {
                if k < i - 1 {
                    assert(r[3*k] == s1[k] && r[3*k+1] == s2[k] && r[3*k+2] == s3[k]);
                }
            }
        }
    }
    r
}
// </vc-code>

fn main() {
}

}