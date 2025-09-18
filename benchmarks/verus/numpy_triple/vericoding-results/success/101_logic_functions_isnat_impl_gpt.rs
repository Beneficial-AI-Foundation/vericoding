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
/* helper modified by LLM (iteration 3): simplified predicate to classify Nat vs Valid without any proof blocks */
spec fn is_nat(d: DateTime64) -> bool {
    match d {
        DateTime64::Nat => true,
        DateTime64::Valid(_) => false,
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
    /* code modified by LLM (iteration 3): implement loop that maps Nat to true and Valid(_) to false; maintain invariants and provide small proofs for existence/non-existence */
    let n = x.len();
    let mut result: Vec<bool> = Vec::new();
    while result.len() < n
        invariant
            result.len() <= n,
            x.len() == n,
            forall|j: int| 0 <= j < result.len() ==> (result@.index(j) == true <==> x@.index(j) == DateTime64::Nat),
            forall|j: int| 0 <= j < result.len() ==> (result@.index(j) == false <==> exists|val: i64| x@.index(j) == DateTime64::Valid(val)),
        decreases (n - result.len()) as int
    {
        let k = result.len();
        let xi = x[k];
        match xi {
            DateTime64::Nat => {
                // set true and show there is no Valid witness
                let b = true;
                proof {
                    assert(!exists|val: i64| xi == DateTime64::Valid(val)) by {
                        assert_forall_by(|val: i64| {
                            ensures(xi != DateTime64::Valid(val));
                            assert(xi == DateTime64::Nat);
                            assert(DateTime64::Nat != DateTime64::Valid(val));
                        });
                    }
                }
                result.push(b);
            }
            DateTime64::Valid(v) => {
                // set false and provide a Valid witness
                let b = false;
                proof {
                    assert(exists|val: i64| xi == DateTime64::Valid(val)) by {
                        let val = v;
                        assert(xi == DateTime64::Valid(val));
                    }
                }
                result.push(b);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}