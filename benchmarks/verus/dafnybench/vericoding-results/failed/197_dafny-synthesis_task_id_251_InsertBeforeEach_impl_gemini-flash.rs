use vstd::prelude::*;

verus! {

// <vc-helpers>
fn seq_to_vec_string(s: Seq<String>) -> (v: Vec<String>)
    ensures
        v.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> v@[i] == s[i],
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            i <= s.len() as usize,
            v.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> v@[j] == s[j],
    {
        v.push(s.index(i as nat).clone());
        i = i + 1;
    }
    v
}

fn vec_to_seq_string(v: Vec<String>) -> (s: Seq<String>)
    ensures
        s.len() == v.len(),
        forall|i: int| 0 <= i < v.len() ==> s[i] == v@[i],
{
    let mut s: Seq<String> = Seq::empty();
    let mut i: usize = 0;
    while i < v.len() as usize
        invariant
            i <= v.len() as usize,
            s.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> s[j] == v@[j],
    {
        s = s.push(v.index(i as nat).clone()); // Using index for seq pushing
        i = i + 1;
    }
    s
}
// </vc-helpers>

// <vc-spec>
#[verifier::exec_allows_no_decreases_clause]
fn insert_before_each(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall|i: int| 0 <= i < s.len() ==> v[2*i] == x && v[2*i + 1] == s[i],
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<String> = Vec::new();
    let l_s = s.len();
    assert(s.len() >= 0) by (nonlinear_arith);
    let mut i: usize = 0;
    while i < l_s as usize
        invariant
            l_s == s.len(),
            i <= l_s as usize,
            v.len() == 2 * i,
            forall|j: int| 0 <= j < (i as int) ==> v@[2 * j] == x && v@[2 * j + 1] == s[j],
    {
        v.push(x.clone());
        v.push(s.index(i as nat).clone());
        i = i + 1;
    }
    proof {
        let final_seq = vec_to_seq_string(v.clone());
        assert(final_seq.len() == v.len());
        assert(v.len() == 2 * s.len()) by (nonlinear_arith);
        assert(final_seq.len() == 2 * s.len());
        assert(forall|j: int| 0 <= j < s.len() ==> #[trigger]final_seq[2 * j] == x && #[trigger]final_seq[2 * j + 1] == s[j]) by {
            assert((i as int) == s.len());
            assert(v.len() == 2 * s.len());
            assert(forall|k: int| 0 <= k < s.len() ==> v@[2 * k] == x && v@[2 * k + 1] == s[k]);
            assert(forall |k: int| 0 <= k < v.len() ==> final_seq[k] == v@[k]);
        }
    }
    vec_to_seq_string(v)
}
// </vc-code>

fn main() {}

}