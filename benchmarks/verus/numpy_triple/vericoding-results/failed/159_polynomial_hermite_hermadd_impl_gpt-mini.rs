// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): max of two nats */
fn max_nat(a: nat, b: nat) -> (result: nat)
    ensures
        result == if a >= b { a } else { b },
{
    if a >= b {
        a
    } else {
        b
    }
}

// </vc-helpers>

// <vc-spec>
fn hermadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==>
            result@[i] as int == (
                if i < c1@.len() && i < c2@.len() {
                    c1@[i] as int + c2@[i] as int
                } else if i < c1@.len() {
                    c1@[i] as int
                } else if i < c2@.len() {
                    c2@[i] as int
                } else {
                    0
                }
            ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement hermadd with usize loop and per-element proof */
    let m = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            result@.len() == i as nat,
            i <= m,
            forall|j: int| 0 <= j && j < i as int ==>
                result@[j] as int == (
                    if j < c1@.len() && j < c2@.len() {
                        c1@[j] as int + c2@[j] as int
                    } else if j < c1@.len() {
                        c1@[j] as int
                    } else {
                        c2@[j] as int
                    }
                ),
        decreases m as nat - i as nat
    {
        let v: i8;
        let idx: int = i as int;
        if i < c1.len() && i < c2.len() {
            v = #[verifier::truncate] ((c1[i] as i16 + c2[i] as i16) as i8);
        } else if i < c1.len() {
            v = c1[i];
        } else {
            v = c2[i];
        }
        result.push(v);
        proof {
            assert(0 <= idx);
            // after push, the newly pushed element is at position idx == i as int
            assert(idx < result@.len());
            if i < c1.len() && i < c2.len() {
                assert(result@[idx] as int == c1@[idx] as int + c2@[idx] as int);
            } else if i < c1.len() {
                assert(result@[idx] as int == c1@[idx] as int);
            } else {
                assert(result@[idx] as int == c2@[idx] as int);
            }
        }
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}