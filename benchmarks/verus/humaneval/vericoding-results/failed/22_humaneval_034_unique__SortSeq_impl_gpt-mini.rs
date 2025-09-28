// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): use Seq::slice free function for specification slices */
fn insert_sorted(v: Vec<i8>, x: i8) -> (res: Vec<i8>)
    requires
        forall|i: int, j: int| 0 <= i < j < v@.len() ==> v@[i] <= v@[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < res@.len() ==> res@[i] <= res@[j],
        res@.len() == v@.len() + 1,
        res@.to_multiset() == v@.to_multiset().insert(x),
{
    let n = v.len();
    let mut out: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            out@.len() == i as int,
            out@ == Seq::slice(v@, 0, i as int),
            forall|p: int, q: int| 0 <= p < q < out@.len() ==> out@[p] <= out@[q],
        decreases n - i
    {
        out.push(v[i]);
        i = i + 1;
    }
    out.push(x);
    let mut j: usize = i;
    while j < n
        invariant
            i as int <= j as int <= n as int,
            out@.len() == j as int + 1,
            out@ == Seq::slice(v@, 0, i as int) + seq![x] + Seq::slice(v@, i as int, j as int),
            forall|p: int, q: int| 0 <= p < q < out@.len() ==> out@[p] <= out@[q],
        decreases n - j
    {
        out.push(v[j]);
        j = j + 1;
    }
    out
}

// </vc-helpers>

// <vc-spec>
fn sort_seq(s: Vec<i8>) -> (sorted: Vec<i8>)
    ensures 
        forall|i: int, j: int| 0 <= i < j < sorted@.len() ==> sorted@[i] <= sorted@[j],
        sorted@.len() == s@.len(),
        s@.to_multiset() == sorted@.to_multiset()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use Seq::slice in invariants and insert_sorted helper */
{
    let n = s.len();
    let mut out: Vec<i8> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k as int <= n as int,
            forall|i: int, j: int| 0 <= i < j < out@.len() ==> out@[i] <= out@[j],
            out@.len() == k as int,
            out@.to_multiset() + Seq::slice(s@, k as int, n as int).to_multiset() == s@.to_multiset(),
        decreases n - k
    {
        out = insert_sorted(out, s[k]);
        k = k + 1;
    }
    out
}

// </vc-code>


}

fn main() {}