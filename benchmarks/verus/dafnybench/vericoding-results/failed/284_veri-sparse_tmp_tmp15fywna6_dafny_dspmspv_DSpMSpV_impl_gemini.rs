// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sum(X_val: Seq<int>, X_crd: Seq<nat>, 
           v_val: Seq<int>, v_crd: Seq<nat>, 
           kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases pX_end + pV_end - (kX + kV)
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] == v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + 
        (if kV < v_val.len() && kX < X_val.len() { v_val[kV as int] * X_val[kX as int] } else { 0 })
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX as int] < v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}

spec fn min(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

spec fn notin(y: nat, x: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != #[trigger] x[i]
}

spec fn index_seq(x: nat, y: Seq<nat>) -> nat
    decreases y.len()
{
    if y.len() == 0 {
        0
    } else if y[0] == x {
        0
    } else {
        1 + index_seq(x, y.subrange(1, y.len() as int))
    }
}

spec fn index(x: nat, y: Seq<nat>) -> nat {
    index_seq(x, y)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): use usize for executable code types and indexing */
proof fn lemma_index_of_sorted(s: Seq<nat>, i: nat)
    requires
        i < s.len(),
        forall|j: int, k: int| 0 <= j < k < s.len() ==> s[j] < s[k],
    ensures
        index(s[i as int], s) == i,
    decreases i,
{
    if i > 0 {
        assert(s[0] < s[i as int]);
        lemma_index_of_sorted(s.subrange(1, s.len() as int), (i - 1) as nat);
    }
}

fn compute_dot_product(X_val: &[int], X_crd: &[nat], v_val: &[int], v_crd: &[nat], 
                       pX_start: usize, pX_end: usize, pV_end: usize) -> (s: int)
    requires
        pX_start <= pX_end,
        pX_end <= X_val.len(),
        pX_end <= X_crd.len(),
        X_val.len() == X_crd.len(),
        pV_end <= v_val.len(),
        pV_end <= v_crd.len(),
        v_val.len() == v_crd.len(),
    ensures
        s == sum(X_val@, X_crd@, v_val@, v_crd@, pX_start as nat, 0, pX_end as nat, pV_end as nat)
{
    let mut kX: usize = pX_start;
    let mut kV: usize = 0;
    let mut s: int = 0;

    while kX < pX_end && kV < pV_end
        invariant
            pX_start <= kX <= pX_end,
            0 <= kV <= pV_end,
            s + sum(X_val@, X_crd@, v_val@, v_crd@, kX as nat, kV as nat, pX_end as nat, pV_end as nat) ==
                sum(X_val@, X_crd@, v_val@, v_crd@, pX_start as nat, 0, pX_end as nat, pV_end as nat),
        decreases (pX_end - kX) + (pV_end - kV)
    {
        if X_crd[kX] == v_crd[kV] {
            s = s + v_val[kV] * X_val[kX];
            kX = kX + 1;
            kV = kV + 1;
        } else if X_crd[kX] < v_crd[kV] {
            kX = kX + 1;
        } else {
            kV = kV + 1;
        }
    }
    s
}
// </vc-helpers>

// <vc-spec>
fn DSpMSpV(X_val: &[int], X_crd: &[nat], X_pos: &[nat], X_crd1: &[nat], X_len: nat,
           v_val: &[int], v_crd: &[nat]) -> (result: Vec<int>)

    requires X_pos.len() >= 1,
             X_val.len() == X_crd.len(),
             (forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> #[trigger] X_pos[i] <= #[trigger] X_pos[j]),
             (forall|i: int| 0 <= i < X_pos.len() ==> 0 <= #[trigger] X_pos[i] <= X_val.len()),

             X_len >= X_crd1.len(),
             (forall|i: int| 0 <= i < X_crd1.len() ==> #[trigger] X_crd1[i] < X_len),

             (X_crd1.len() < X_pos.len()),
             (forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> #[trigger] X_crd1[i] < #[trigger] X_crd1[j]),

             (v_val.len() == v_crd.len()),

    ensures result.len() == X_len,
            (forall|i: int| 0 <= i < result.len() ==> {
        let idx = index(i as nat, X_crd1@);
        #[trigger] result[i] == if idx < X_crd1.len() {
            sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                X_pos[idx as int + 1], v_val.len() as nat)
        } else {
            0
        }})
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): use usize for loop counters and indexing */
{
    let mut result = Vec::from_elem(0, X_len as usize);

    let mut p: usize = 0;
    while p < X_crd1.len()
        invariant
            0 <= p <= X_crd1.len(),
            X_pos.len() >= 1,
            X_val.len() == X_crd.len(),
            (forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j]),
            (forall|i: int| 0 <= i < X_pos.len() ==> 0 <= X_pos[i] <= X_val.len()),
            X_len >= X_crd1.len(),
            (forall|i: int| 0 <= i < X_crd1.len() ==> X_crd1[i] < X_len),
            (X_crd1.len() < X_pos.len()),
            (forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> X_crd1[i] < X_crd1[j]),
            (v_val.len() == v_crd.len()),
            result.len() == X_len,
            forall|i: int| 0 <= i < result.len() ==> {
                let idx = index(i as nat, X_crd1@);
                #[trigger] result[i] == if idx < p as nat {
                     sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                        X_pos[idx as int + 1], v_val.len() as nat)
                } else {
                    0
                }
            },
        decreases X_crd1.len() - p
    {
        let row_idx = X_crd1[p];
        let pX_start = X_pos[p] as usize;
        let pX_end = X_pos[p + 1] as usize;

        let dot_product = compute_dot_product(X_val, X_crd, v_val, v_crd, 
                                              pX_start, pX_end, v_val.len());
        proof {
            lemma_index_of_sorted(X_crd1@, p as nat);
        }
        
        result.set(row_idx as usize, dot_product);

        p = p + 1;
    }

    result
}
// </vc-code>

}
fn main() {}