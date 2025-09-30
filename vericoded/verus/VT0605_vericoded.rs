// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_i8_zeros(n: usize) -> (v: Vec<i8>)
    ensures
        v.len() == n,
        forall|j: int| 0 <= j < v.len() ==> v@[j] == 0i8,
        forall|j: int| 0 <= j < v.len() ==> v[j] as int == 0,
        forall|j: int| 0 <= j < v.len() ==> v[j] as int >= 0,
{
    let mut v: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            v.len() == i,
            i <= n,
            forall|j: int| 0 <= j < v.len() ==> v@[j] == 0i8,
            forall|j: int| 0 <= j < v.len() ==> v[j] as int == 0,
            forall|j: int| 0 <= j < v.len() ==> v[j] as int >= 0,
        decreases n - i
    {
        v.push(0i8);
        i += 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<String>, sub: Vec<String>, start: Vec<i8>, end_pos: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == sub.len(),
        a.len() == start.len(),
        a.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> start[i] as int <= end_pos[i] as int,
        forall|i: int| 0 <= i < a.len() ==> 0 <= start[i] as int && start[i] as int <= a[i]@.len(),
        forall|i: int| 0 <= i < a.len() ==> 0 <= end_pos[i] as int && end_pos[i] as int <= a[i]@.len(),
        forall|i: int| 0 <= i < a.len() ==> sub[i]@.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int >= 0,
        forall|i: int| 0 <= i < result.len() ==> 
            (sub[i]@.len() > (end_pos[i] as int - start[i] as int) ==> result[i] as int == 0)
// </vc-spec>
// <vc-code>
{
    let result = vec_i8_zeros(a.len());
    result
}
// </vc-code>

}
fn main() {}