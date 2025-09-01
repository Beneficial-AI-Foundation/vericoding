use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
fn contains(v: &Vec<i32>, x: i32) -> (ret: bool)
    ensures ret == exists|i: int| 0 <= i < v.len() && v[i] == x
{
    let mut i = 0;
    while i < v.len()
        invariant 0 <= i <= v.len()
        invariant forall|j: int| #![trigger] 0 <= j < i ==> v@[j] != x
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

spec fn is_distinct_prefix(a: Seq<i32>, idx: int, res: Seq<i32>) -> bool {
    (res.len() <= idx) &&
    forall|i: int| 0 <= i < idx ==> exists|j: int| 0 <= j < res.len() && res[j] == a[i] &&
        forall|k: int| 0 <= k < res.len() && res[k] == a[i] ==> k == j &&
        forall|l: int| 0 <= l < idx && a[l] == a[i] ==> l >= j &&
    forall|p: int, q: int| 0 <= p < q < res.len() ==> res[p] != res[q]
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant 0 <= i <= a.len()
        invariant is_distinct_prefix(a@, i, result@)
    {
        let x = a[i];
        if !contains(&result, x) {
            result.push(x);
        }
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}