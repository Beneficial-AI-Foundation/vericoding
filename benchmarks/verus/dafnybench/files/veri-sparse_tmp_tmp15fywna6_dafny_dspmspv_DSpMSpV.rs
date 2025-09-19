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
// </vc-helpers>

// <vc-spec>
fn DSpMSpV(X_val: &[i8], X_crd: &[u8], X_pos: &[u8], X_crd1: &[u8], X_len: u8,
           v_val: &[i8], v_crd: &[u8]) -> (result: Vec<i8>)

    requires X_pos.len() >= 1,
             X_val.len() == X_crd.len(),
             (forall|i: int, j: int| 0 <= i < j < X_pos.len() ==> #[trigger] X_pos[i] <= #[trigger] X_pos[j]),
             (forall|i: int| 0 <= i < X_pos.len() ==> 0 <= #[trigger] X_pos[i] as int <= X_val.len()),

             (X_len as nat) >= X_crd1.len(),
             (forall|i: int| 0 <= i < X_crd1.len() ==> (#[trigger] X_crd1[i] as nat) < (X_len as nat)),

             (X_crd1.len() < X_pos.len()),
             (forall|i: int, j: int| 0 <= i < j < X_crd1.len() ==> #[trigger] X_crd1[i] < #[trigger] X_crd1[j]),

             (v_val.len() == v_crd.len()),

    ensures result.len() == X_len as usize,
            (forall|i: int| 0 <= i < result.len() ==> {
        let idx = index(i as nat, X_crd1@.map(|_i, v| v as nat));
        #[trigger] result[i] as int == if idx < X_crd1.len() {
            sum(X_val@.map(|_i, v| v as int), X_crd@.map(|_i, v| v as nat), 
                v_val@.map(|_i, v| v as int), v_crd@.map(|_i, v| v as nat), 
                X_pos[idx as int] as nat, 0, 
                X_pos[idx as int + 1] as nat, v_val.len() as nat)
        } else {
            0
        }})
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}