use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn append_array_to_seq_lemma(s: Seq<i32>, a: &Vec<i32>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        a@[i] == a[i]
{
}

proof fn vec_to_seq_conversion(a: &Vec<i32>) -> (seq: Seq<i32>)
    ensures
        seq.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> seq[i] == a@[i]
{
    let mut seq = Seq::empty();
    let mut j: int = 0;
    
    while j < a.len()
        invariant
            0 <= j <= a.len(),
            seq.len() == j,
            forall|k: int| 0 <= k < j ==> seq[k] == a@[k]
    {
        seq = seq.add(a@[j]);
        j = j + 1;
    }
    
    seq
}
// </vc-helpers>

// <vc-spec>
fn append_array_to_seq(s: Seq<i32>, a: &Vec<i32>) -> (r: Seq<i32>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
        forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut r = s;
    let mut i: int = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            r.len() == s.len() + i,
            forall|j: int| 0 <= j < s.len() ==> r[j] == s[j],
            forall|j: int| 0 <= j < i ==> r[s.len() + j] == a@[j]
    {
        append_array_to_seq_lemma(s, a, i);
        r = r.add(a@[i]);
        i = i + 1;
    }
    
    r
}
// </vc-code>

fn main() {}

}