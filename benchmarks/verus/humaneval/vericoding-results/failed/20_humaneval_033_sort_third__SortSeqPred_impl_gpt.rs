// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): eliminated chained comparisons with casts inside quantifiers/invariants to fix parsing issues */
fn argmin_pos(v: &Vec<i8>, idxs: &Vec<usize>, start: usize) -> (pos: usize)
    requires
        start < idxs.len(),
        forall|k: int| 0 <= k && k < idxs.len() as int ==> 0 <= (idxs@[k] as int) && (idxs@[k] as int) < v.len() as int,
    ensures
        start <= pos,
        pos < idxs.len(),
        forall|k: int| start as int <= k && k < idxs.len() as int ==> (v@[idxs@[pos as int] as int] as int) <= (v@[idxs@[k] as int] as int),
{
    let mut best: usize = start;
    let mut k: usize = start + 1;
    while k < idxs.len()
        invariant
            start < idxs.len(),
            start <= best < idxs.len(),
            (start + 1 <= k) && (k <= idxs.len()),
            forall|t: int| (start as int <= t) && (t < k as int) ==> (v@[idxs@[best as int] as int] as int) <= (v@[idxs@[t] as int] as int),
            forall|t: int| 0 <= t && t < idxs.len() as int ==> 0 <= (idxs@[t] as int) && (idxs@[t] as int) < v.len() as int,
        decreases idxs.len() - k
    {
        if v[idxs[k]] < v[idxs[best]] {
            best = k;
        }
        k = k + 1;
    }
    best
}
// </vc-helpers>

// <vc-spec>
fn sort_seq_pred(s: Vec<i8>, p: Vec<bool>) -> (sorted: Vec<i8>)
  requires s.len() == p.len(),
  ensures 
    sorted.len() == s.len(),
    forall|i: int, j: int| 0 <= i < j < sorted.len() && p[i] && p[j] ==> sorted[i] as int <= sorted[j] as int,
    s@.to_multiset() == sorted@.to_multiset(),
    forall|i: int| 0 <= i < s.len() && !p[i] ==> sorted[i] == s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): replaced chained comparisons with casts in quantifiers by conjunctions to fix parsing */
    let n = s.len();
    let mut res = s.clone();

    // collect indices where p is true, in increasing order
    let mut idxs: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            idxs.len() <= i,
            res.len() == n,
            forall|k: int| 0 <= k && k < idxs.len() as int ==> 0 <= (idxs@[k] as int) && (idxs@[k] as int) < n as int,
            forall|u: int, v_: int| (0 <= u) && (u < v_) && (v_ < idxs.len() as int) ==> (idxs@[u] as int) < (idxs@[v_] as int),
            forall|k: int| 0 <= k && k < idxs.len() as int ==> p@[idxs@[k] as int],
        decreases n - i
    {
        if p[i] {
            idxs.push(i);
        }
        i = i + 1;
    }

    let m = idxs.len();

    // selection sort among the indices in idxs
    let mut t: usize = 0;
    while t < m
        invariant
            res.len() == n,
            t <= m,
            forall|k: int| 0 <= k && k < idxs.len() as int ==> 0 <= (idxs@[k] as int) && (idxs@[k] as int) < n as int,
            forall|u: int, v_: int| (0 <= u) && (u < v_) && (v_ < idxs.len() as int) ==> (idxs@[u] as int) < (idxs@[v_] as int),
            forall|k: int| 0 <= k && k < idxs.len() as int ==> p@[idxs@[k] as int],
            forall|u: int, v_: int| (0 <= u) && (u < v_) && (v_ < t as int) ==> (res@[idxs@[u] as int] as int) <= (res@[idxs@[v_] as int] as int),
        decreases m - t
    {
        let pos = argmin_pos(&res, &idxs, t);
        let a = idxs[t];
        let b = idxs[pos];
        if a != b {
            let tmp = res[a];
            res[a] = res[b];
            res[b] = tmp;
        }
        t = t + 1;
    }

    // length preserved
    assert(res.len() == s.len());

    // unchanged where predicate is false (we never touched indices outside idxs)
    assert(forall|i_: int| 0 <= i_ && i_ < n as int && !p@[i_] ==> res@[i_] == s@[i_]);

    // sorted among indices with predicate true
    assert(forall|i_: int, j_: int|
        0 <= i_ && i_ < j_ && j_ < n as int && p@[i_] && p@[j_] ==> (res@[i_] as int) <= (res@[j_] as int)
    ) by {
        assert forall|i0: int, j0: int| (0 <= i0) && (i0 < j0) && (j0 < idxs.len() as int) ==> (res@[idxs@[i0] as int] as int) <= (res@[idxs@[j0] as int] as int) by {};
    };

    // multiset preserved (only swaps within res occur)
    assert(s@.to_multiset() == res@.to_multiset());

    res
}
// </vc-code>


}

fn main() {}