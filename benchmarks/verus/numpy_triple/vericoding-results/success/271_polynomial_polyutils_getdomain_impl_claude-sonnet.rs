// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn find_min(x: &Vec<i8>) -> (result: i8)
    requires x@.len() > 0,
    ensures
        exists|i: int| 0 <= i < x@.len() && x@[i] == result,
        forall|i: int| 0 <= i < x@.len() ==> result as int <= x@[i] as int,
{
    let mut min_val = x[0];
    let mut i = 1;
    while i < x.len()
        invariant
            1 <= i <= x@.len(),
            exists|j: int| 0 <= j < i && x@[j] == min_val,
            forall|j: int| 0 <= j < i ==> min_val as int <= x@[j] as int,
        decreases x@.len() - i,
    {
        if x[i] < min_val {
            min_val = x[i];
        }
        i += 1;
    }
    min_val
}

fn find_max(x: &Vec<i8>) -> (result: i8)
    requires x@.len() > 0,
    ensures
        exists|i: int| 0 <= i < x@.len() && x@[i] == result,
        forall|i: int| 0 <= i < x@.len() ==> x@[i] as int <= result as int,
{
    let mut max_val = x[0];
    let mut i = 1;
    while i < x.len()
        invariant
            1 <= i <= x@.len(),
            exists|j: int| 0 <= j < i && x@[j] == max_val,
            forall|j: int| 0 <= j < i ==> x@[j] as int <= max_val as int,
        decreases x@.len() - i,
    {
        if x[i] > max_val {
            max_val = x[i];
        }
        i += 1;
    }
    max_val
}
// </vc-helpers>

// <vc-spec>
fn getdomain(x: Vec<i8>) -> (result: Vec<i8>)
    requires x@.len() > 0,
    ensures
        result@.len() == 2,
        result@[0] as int <= result@[1] as int,
        forall|i: int| 0 <= i < x@.len() ==> result@[0] as int <= x@[i] as int && x@[i] as int <= result@[1] as int,
        exists|i: int| 0 <= i < x@.len() && x@[i] as int == result@[0] as int,
        exists|j: int| 0 <= j < x@.len() && x@[j] as int == result@[1] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clauses to loops */
    let min_val = find_min(&x);
    let max_val = find_max(&x);
    let mut result = Vec::new();
    result.push(min_val);
    result.push(max_val);
    result
}
// </vc-code>


}
fn main() {}