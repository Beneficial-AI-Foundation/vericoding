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

// <vc-helpers>
proof fn lemma_index_bounds(x: nat, y: Seq<nat>)
    ensures index(x, y) <= y.len()
    decreases y.len()
{
    if y.len() == 0 {
    } else if y[0] == x {
    } else {
        lemma_index_bounds(x, y.subrange(1, y.len() as int));
    }
}

proof fn lemma_index_correct(x: nat, y: Seq<nat>)
    requires index(x, y) < y.len()
    ensures y[index(x, y) as int] == x
    decreases y.len()
{
    if y.len() == 0 {
    } else if y[0] == x {
    } else {
        lemma_index_correct(x, y.subrange(1, y.len() as int));
    }
}

proof fn lemma_index_not_found(x: nat, y: Seq<nat>)
    requires index(x, y) >= y.len()
    ensures notin(x, y)
    decreases y.len()
{
    if y.len() == 0 {
    } else if y[0] == x {
    } else {
        lemma_index_not_found(x, y.subrange(1, y.len() as int));
    }
}

fn compute_sum(X_val: &[int], X_crd: &[nat], v_val: &[int], v_crd: &[nat], 
               kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> (result: int)
    requires kX <= pX_end,
             kV <= pV_end,
             pX_end <= X_val.len(),
             pV_end <= v_val.len(),
             X_val.len() == X_crd.len(),
             v_val.len() == v_crd.len(),
    ensures result == sum(X_val@, X_crd@, v_val@, v_crd@, kX, kV, pX_end, pV_end),
    decreases pX_end + pV_end - (kX + kV),
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX] == v_crd[kV] {
        let prod = if kV < v_val.len() && kX < X_val.len() { 
            v_val[kV] * X_val[kX] 
        } else { 
            0 
        };
        let rest = compute_sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end);
        rest + prod
    } else if kX < X_crd.len() && kV < v_crd.len() && X_crd[kX] < v_crd[kV] {
        compute_sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        compute_sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}
// </vc-helpers>

// <vc-spec>
fn DSpMSpV(X_val: &[int], X_crd: &[nat], X_pos: &[nat], X_crd1: &[nat], X_len: nat,
           v_val: &[int], v_crd: &[nat]) -> (result: Vec<int>)
    // X requirements 
    requires X_pos.len() >= 1,
    requires X_val.len() == X_crd.len(),
    requires forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> #[trigger] X_pos[i] <= #[trigger] X_pos[j],
    requires forall|i: int| 0 <= i < X_pos.len() ==> 0 <= #[trigger] X_pos[i] <= X_val.len(),

    requires X_len >= X_crd1.len(),
    requires forall|i: int| 0 <= i < X_crd1.len() ==> #[trigger] X_crd1[i] < X_len,

    requires X_crd1.len() < X_pos.len(),
    requires forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> #[trigger] X_crd1[i] < #[trigger] X_crd1[j],

    // v requirements 
    requires v_val.len() == v_crd.len(),

    ensures result.len() == X_len,
    ensures forall|i: int| 0 <= i < result.len() ==> {
        let idx = index(i as nat, X_crd1@);
        #[trigger] result[i] == if idx < X_crd1.len() {
            sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                X_pos[idx as int + 1], v_val.len() as nat)
        } else {
            0
        }
    }
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::with_capacity(X_len);
    
    let mut i: nat = 0;
    while i < X_len
        invariant result.len() == i,
        invariant i <= X_len,
        invariant forall|j: int| 0 <= j < result.len() ==> {
            let idx = index(j as nat, X_crd1@);
            #[trigger] result[j] == if idx < X_crd1.len() {
                sum(X_val@, X_crd@, v_val@, v_crd@, X_pos[idx as int], 0, 
                    X_pos[idx as int + 1], v_val.len() as nat)
            } else {
                0
            }
        }
    {
        proof {
            lemma_index_bounds(i, X_crd1@);
        }
        
        let idx = index(i, X_crd1@);
        
        let val = if idx < X_crd1.len() {
            proof {
                lemma_index_correct(i, X_crd1@);
                assert(X_crd1[idx as int] == i);
            }
            compute_sum(X_val, X_crd, v_val, v_crd, 
                       X_pos[idx], 0, X_pos[idx + 1], v_val.len() as nat)
        } else {
            proof {
                lemma_index_not_found(i, X_crd1@);
            }
            0
        };
        
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}

}