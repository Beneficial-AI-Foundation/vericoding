// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let len = x1.len();
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            forall |j: int| 0 <= j < i ==> #[trigger] result@[j] as int == x1@[j] as int + x2@[j] as int,
        decreases len - i
    {
        result.push(x1[i] + x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}