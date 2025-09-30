// <vc-preamble>
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq, Clone, Copy)]
pub enum DateTime64 {
    Valid(i64),
    Nat,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added spec function for Nat check */
pub open spec fn is_nat_dt(d: DateTime64) -> bool {
    match d {
        DateTime64::Nat => true,
        DateTime64::Valid(_) => false,
    }
}

/* helper modified by LLM (iteration 2): lemma connecting non-Nat with existence of a Valid witness */
pub proof fn lemma_not_nat_iff_exists_valid(d: DateTime64)
    ensures
        (d != DateTime64::Nat) <==> (exists|v: i64| d == DateTime64::Valid(v)),
{
    match d {
        DateTime64::Nat => {
            assert(!(exists|v: i64| d == DateTime64::Valid(v)));
        }
        DateTime64::Valid(v) => {
            assert(d != DateTime64::Nat);
            assert(exists|v2: i64| d == DateTime64::Valid(v2)) by {
                assert(d == DateTime64::Valid(v));
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn isnat(x: Vec<DateTime64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == true <==> x@.index(i) == DateTime64::Nat),
        forall|i: int| 0 <= i < x.len() ==> 
            (result@.index(i) == false <==> exists|val: i64| x@.index(i) == DateTime64::Valid(val)),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): strengthen loop proof to establish both equivalences for the newly appended index */
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            res.len() == i,
            forall|j: int| 0 <= j && j < i as int ==>
                (res@.index(j) == true <==> x@.index(j) == DateTime64::Nat),
            forall|j: int| 0 <= j && j < i as int ==>
                (res@.index(j) == false <==> exists|val: i64| x@.index(j) == DateTime64::Valid(val)),
        decreases x.len() - i
    {
        let xi = x[i];
        let b = match xi {
            DateTime64::Nat => true,
            DateTime64::Valid(_) => false,
        };
        res.push(b);
        proof {
            let j: int = i as int; // index of the newly appended element
            assert(0 <= j && j < res.len() as int);
            assert(res@.index(j) == b);
            assert(x@.index(j) == xi);
            match xi {
                DateTime64::Nat => {
                    assert(b == true);
                    // First invariant for j: both sides true
                    assert(res@.index(j) == true);
                    assert(x@.index(j) == DateTime64::Nat);
                    // Second invariant for j: both sides false
                    assert(!(exists|val: i64| x@.index(j) == DateTime64::Valid(val)));
                }
                DateTime64::Valid(v) => {
                    assert(b == false);
                    // First invariant for j: both sides false
                    assert(res@.index(j) == false);
                    assert(x@.index(j) != DateTime64::Nat);
                    // Second invariant for j: both sides true
                    assert(exists|val: i64| x@.index(j) == DateTime64::Valid(val)) by {
                        assert(x@.index(j) == DateTime64::Valid(v));
                    };
                }
            }
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}