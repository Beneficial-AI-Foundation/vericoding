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
/* code modified by LLM (iteration 3): [added assertion to prove loop invariant] */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                (result@.index(j) == true <==> x@.index(j) == DateTime64::Nat),
            forall|j: int| 0 <= j < i as int ==> 
                (result@.index(j) == false <==> exists|val: i64| x@.index(j) == DateTime64::Valid(val)),
        decreases x.len() - i
    {
        match x[i] {
            DateTime64::Nat => {
                result.push(true);
            }
            DateTime64::Valid(val) => {
                result.push(false);
                assert(x@.index(i as int) == DateTime64::Valid(val));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}