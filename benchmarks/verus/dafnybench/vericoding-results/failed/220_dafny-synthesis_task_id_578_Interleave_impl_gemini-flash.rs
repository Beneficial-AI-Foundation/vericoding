use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_push<T>(s: Seq<T>, elem: T) -> (result: Seq<T>)
    ensures
        result.len() == s.len() + 1,
        forall|i: int| #![trigger result[i]] 0 <= i && (i as nat) < s.len() ==> result[i] == s[i],
        result[s.len() as int] == elem,
{
    s.push(elem)
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
    let s_len = s1.len();
    let mut r: Seq<int> = Seq::<int>::new_empty();
    let mut i: int = 0;

    while i < s_len
        invariant
            i <= s_len,
            r.len() == 3 * i,
            forall|j: int| #![trigger r[3 * j]] 0 <= j && j < i ==> r[3 * j] == s1[j as nat] && r[3 * j + 1] == s2[j as nat] && r[3 * j + 2] == s3[j as nat],
    {
        let i_nat = i as nat;
        r = seq_push(r, s1[i_nat]);
        proof {
            // These assertions are now directly provable by the postconditions of seq_push.
            assert(r.len() == 3 * i + 1);
            assert(r[3 * i] == s1[i_nat]);
        }

        r = seq_push(r, s2[i_nat]);
        proof {
            assert(r.len() == 3 * i + 2);
            assert(r[3 * i + 1] == s2[i_nat]);
        }

        r = seq_push(r, s3[i_nat]);
        proof {
            assert(r.len() == 3 * i + 3);
            assert(r[3 * i + 2] == s3[i_nat]);
        }

        i = i + 1;
    }
    r
}
// </vc-code>

fn main() {
}

}