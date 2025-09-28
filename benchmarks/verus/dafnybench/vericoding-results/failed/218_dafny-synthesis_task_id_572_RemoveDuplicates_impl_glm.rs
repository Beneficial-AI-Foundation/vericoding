use vstd::prelude::*;

verus! {

// <vc-helpers>
exec fn vec_contains(v: &Vec<i32>, x: i32) -> (b: bool)
    ensures
        b == v@.contains(x)
{
    let mut found = false;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            found <==> exists|j: int| 0 <= j < i && v@[j] == x
    {
        if v[i] == x {
            found = true;
        }
        i += 1;
    }
    found
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) <==> exists|i: int| 0 <= i < a.len() && a[i] == x,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    for i in 0..a.len()
        invariant
            forall|k: int, l: int| 0 <= k < l < res.len() ==> res@[k] != res@[l],
            forall|x: i32| res@.contains(x) <==> exists|j: int| 0 <= j < i && a[j] == x
    {
        if !vec_contains(&res, a[i]) {
            res.push(a[i]);
        }
    }
    res
}
// </vc-code>

fn main() {
}

}