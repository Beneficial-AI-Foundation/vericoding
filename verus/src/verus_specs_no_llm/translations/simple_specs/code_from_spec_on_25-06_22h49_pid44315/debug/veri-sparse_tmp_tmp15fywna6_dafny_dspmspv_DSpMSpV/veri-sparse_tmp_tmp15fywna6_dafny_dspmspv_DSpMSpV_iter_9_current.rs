use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper function to compute sum of products of matching coordinates
spec fn sum(X_val: Vec<int>, X_crd: Vec<nat>, v_val: Vec<int>, v_crd: Vec<nat>, kX: nat, kV: nat, pX_end: nat, pV_end: nat) -> int
    decreases (pX_end - kX) + (pV_end - kV)
    requires X_val.len() == X_crd.len()
    requires pX_end <= X_crd.len()
    requires kX <= pX_end
    requires v_val.len() == v_crd.len()
    requires pV_end <= v_crd.len()
    requires kV <= pV_end
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
    decreases (pX_end - kX) + (pV_end - kV)
    requires x.len() == X_crd.len()
    requires pX_end <= X_crd.len()
    requires kX <= pX_end
    requires v_crd.len() == v_val.len()
    requires pV_end <= v_crd.len()
    requires kV <= pV_end
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
            let tail = y.subrange(1, y.len() as int);
            let tail_result = index_seq(x, tail);
            if tail_result < tail.len() {
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

// Simple executable function to demonstrate verification
fn test_min(a: usize, b: usize) -> (result: usize)
    ensures result == min(a as nat, b as nat)
{
    if a <= b { a } else { b }
}

// Proof function to verify properties with more careful assertions
proof fn test_index_seq_properties()
{
    let s = seq![1nat, 2nat, 3nat];
    
    // Apply the lemma to establish properties
    lemma_index_seq_correctness(2nat, s);
    lemma_index_seq_correctness(5nat, s);
    
    // Test finding element that exists
    assert(s.len() == 3);
    assert(s[1] == 2nat);
    let idx2 = index_seq(2nat, s);
    assert(idx2 < s.len());
    assert(s[idx2 as int] == 2nat);
    
    // Test finding element that doesn't exist
    let idx5 = index_seq(5nat, s);
    assert(idx5 == s.len());
    
    // Test notin_seq properties
    assert(notin_seq(5nat, s));
    assert(!notin_seq(2nat, s));
}

// Additional helper proof to establish properties step by step
proof fn lemma_index_seq_correctness(x: nat, s: Seq<nat>)
    ensures index_seq(x, s) <= s.len()
    ensures index_seq(x, s) < s.len() ==> s[index_seq(x, s) as int] == x
    ensures index_seq(x, s) == s.len() ==> notin_seq(x, s)
    decreases s.len()
{
    if s.len() == 0 {
        // Base case: empty sequence
    } else if s[0] == x {
        // Found at position 0
    } else {
        // Recursive case: search in tail
        let tail = s.subrange(1, s.len() as int);
        
        // Apply inductive hypothesis
        lemma_index_seq_correctness(x, tail);
        
        let tail_result = index_seq(x, tail);
        
        if tail_result < tail.len() {
            // Found in tail at position tail_result
            assert(tail[tail_result as int] == x);
            assert(s[1 + tail_result as int] == x);
        } else {
            // Not found in tail
            assert(tail_result == tail.len());
            assert(notin_seq(x, tail));
            
            // Prove that x is not anywhere in s
            assert(forall|i: int| 0 <= i < s.len() ==> {
                if i == 0 {
                    s[i] != x
                } else {
                    s[i] == tail[i - 1] && tail[i - 1] != x
                }
            });
        }
    }
}

}