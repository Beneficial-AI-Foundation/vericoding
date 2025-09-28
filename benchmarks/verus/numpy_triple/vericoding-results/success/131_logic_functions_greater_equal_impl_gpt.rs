// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn ge_antisym(a: int, b: int)
    requires
        a >= b,
        b >= a,
    ensures
        a == b,
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] as int >= x2@[i] as int),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] as int >= x1@[i] as int) ==> x1@[i] as int == x2@[i] as int,

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0usize;

    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == x1.len(),
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < result.len() ==> (result@[j] <==> x1@[j] as int >= x2@[j] as int),
        decreases n - i
    {
        let b: bool = x1[i] >= x2[i];
        result.push(b);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}