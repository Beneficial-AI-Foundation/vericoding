// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn id_int(x: int) -> int { x }
// </vc-helpers>

// <vc-spec>
fn append(a: &Vec<i32>, b: i32) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + 1,
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i],
        result[a.len() as int] == b,
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int <= a.len() as int,
            result.len() as int == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] == a[j],
        decreases (a.len() - i) as int
    {
        let v = a[i];
        result.push(v);
        i += 1;
    }
    proof {
        assert(forall|j: int| 0 <= j < a.len() as int ==> result[j] == a[j]);
    }
    result.push(b);
    result
}
// </vc-code>

}
fn main() {}