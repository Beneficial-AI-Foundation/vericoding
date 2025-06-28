use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to compute sum of products of matching coordinates
spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases (if pX_end >= kX { pX_end - kX } else { 0 }) + (if pV_end >= kV { pV_end - kV } else { 0 })
    requires X_val.len() == X_crd.len()
    requires pX_end <= X_crd.len()
    requires kX <= X_crd.len()
    requires v_val.len() == v_crd.len()
    requires pV_end <= v_crd.len()
    requires kV <= v_crd.len()
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

spec fn notin(y: nat, x: Vec<nat>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases (if pX_end >= kX { pX_end - kX } else { 0 }) + (if pV_end >= kV { pV_end - kV } else { 0 })
    requires x.len() == X_crd.len()
    requires pX_end <= X_crd.len()
    requires kX <= X_crd.len()
    requires v_crd.len() == v_val.len()
    requires pV_end <= v_crd.len()
    requires kV <= v_crd.len()
{
    if pV_end <= kV || pX_end <= kX {
        0
    } else if X_crd[kX as int] == v_crd[kV as int] {
        notin(y, x, X_crd, v_val, v_crd, kX + 1, kV + 1, pX_end, pV_end) + v_val[kV as int] * x[kX as int]
    } else if X_crd[kX as int] < v_crd[kV as int] {
        notin(y, x, X_crd, v_val, v_crd, kX + 1, kV, pX_end, pV_end)
    } else {
        notin(y, x, X_crd, v_val, v_crd, kX, kV + 1, pX_end, pV_end)
    }
}

spec fn index_seq(x: nat, y: Seq<nat>) -> nat
    decreases y.len()
    ensures index_seq(x, y) <= y.len()
    ensures index_seq(x, y) < y.len() ==> y[index_seq(x, y) as int] == x
    ensures index_seq(x, y) == y.len() ==> forall|i: int| 0 <= i < y.len() ==> y[i] != x
{
    if y.len() == 0 {
        0
    } else {
        if y[0] == x {
            0
        } else {
            let tail_result = index_seq(x, y.subrange(1, y.len() as int));
            if tail_result < y.subrange(1, y.len() as int).len() {
                1 + tail_result
            } else {
                y.len()
            }
        }
    }
}

spec fn min(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

spec fn notin_seq(y: nat, x: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < x.len() ==> y != x[i]
}

}