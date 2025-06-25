use vstd::prelude::*;

verus! {

spec fn sum(X_val: &[int], X_crd: &[nat],
           v_val: &[int], v_crd: &[nat], kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    recommends
        X_val.len() == X_crd.len(),
        pX_end <= X_crd.len(),
        0 <= kX <= X_crd.len(),
        v_val.len() == v_crd.len(),
        pV_end <= v_crd.len(),
        0 <= kV <= v_crd.len(),
    decreases pX_end + pV_end - kX - kV
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if X_crd[kX as int] == v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV as int] * X_val[kX as int]
    } else if X_crd[kX as int] < v_crd[kV as int] {
        sum(X_val, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        sum(X_val, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}

spec fn min(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

spec fn notin(y: nat, x: &[nat]) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != x[i]
}

spec fn notin_seq(y: nat, x: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != x[i]
}

spec fn index_seq(x: nat, y: Seq<nat>) -> nat
    ensures |ret: nat| ret >= y.len() ==> notin_seq(x, y),
    ensures |ret: nat| ret < y.len() ==> y[ret as int] == x,
    decreases y.len()
{
    if y.len() == 0 {
        0
    } else {
        if y[0] == x {
            0
        } else {
            1 + index_seq(x, y.subrange(1, y.len() as int))
        }
    }
}

spec fn index(x: nat, y: &[nat]) -> nat
    ensures |ret: nat| ret >= y.len() ==> notin(x, y),
    ensures |ret: nat| ret < y.len() ==> y[ret as int] == x
{
    index_seq(x, y@)
}

pub fn DSpMSpV(X_val: &[int], X_crd: &[nat], X_pos: &[nat],
               X_crd1: &[nat], X_len: nat,
               v_val: &[int], v_crd: &[nat]) -> (y: Vec<int>)
    requires
        X_pos.len() >= 1,
        X_val.len() == X_crd.len(),
        forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> X_pos[i] <= X_pos[j],
        forall|i: int| 0 <= i < X_pos.len() ==> 0 <= X_pos[i] <= X_val.len(),
        X_len >= X_crd1.len(),
        forall|i: int| 0 <= i < X_crd1.len() ==> X_crd1[i] < X_len,
        X_crd1.len() < X_pos.len(),
        forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> X_crd1[i] < X_crd1[j],
        v_val.len() == v_crd.len()
    ensures
        y.len() == X_len,
        forall|i: int| 0 <= i < y.len() ==> 
            y[i] == 
                if index(i as nat, X_crd1) < X_crd1.len() {
                    sum(X_val, X_crd, v_val, v_crd, X_pos[index(i as nat, X_crd1) as int], 0, X_pos[index(i as nat, X_crd1) as int + 1], v_val.len())
                } else {
                    0
                }
{
    unimplemented!()
}

pub fn Main() {
    
}

}