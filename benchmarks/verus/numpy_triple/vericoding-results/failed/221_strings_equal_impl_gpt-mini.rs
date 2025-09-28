// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compare two Strings by bytes */
fn strings_equal(x: &String, y: &String) -> bool {
    let bx = x.as_bytes();
    let by = y.as_bytes();
    if bx.len() != by.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < bx.len()
        invariant
            0 <= i as int && i as int <= bx.len() as int,
        decreases bx.len() as int - i as int
    {
        if bx[i] != by[i] {
            return false;
        }
        i += 1;
    }
    true
}

// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build result Vec by comparing strings via helper comparing bytes */
    let mut result: Vec<bool> = Vec::<bool>::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i as int && i as int <= x1.len() as int,
            result.len() == i,
            forall|j: int| 0 <= j && j < i as int ==> result@[j] == (x1@[j] == x2@[j]),
        decreases x1.len() as int - i as int
    {
        let xi = x1.get(i).unwrap();
        let yi = x2.get(i).unwrap();
        let b = strings_equal(xi, yi);
        result.push(b);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}