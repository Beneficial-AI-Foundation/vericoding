use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
proof fn in_array_works(a: Seq<i32>, x: i32, i: int)
    requires
        0 <= i < a.len(),
        a[i] == x,
    ensures
        in_array(a, x),
{
    reveal(in_array);
    assert(exists|i: int| 0 <= i < a.len() && a[i] == x);
}

proof fn push_distinct<T>(v: Vec<T>, x: T)
    requires
        v@.distinct(),
        !v.contains(&x),
    ensures
        (v.push(x))@.distinct(),
{
    reveal(Vec::contains);
    assert forall|i: int, j: int| 0 <= i < j < (v.push(x))@.len() implies (v.push(x))@[i] != (v.push(x))@[j] by {
        if j < v@.len() {
            assert(v@.distinct());
        } else {
            assert((v.push(x))@[j] == x);
            assert((v.push(x))@[i] == v@[i]);
            assert(!v.contains(&x));
        }
    }
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
    let mut res: Vec<i32> = Vec::new();
    for i in 0..a.len()
        invariant
            forall|j: int| 0 <= j < res@.len() ==> exists|k: int| 0 <= k < i && a@[k] == res@[j],
            res@.distinct(),
    {
        let x = a[i];
        if !res.contains(&x) {
            let old_res = res;
            res.push(x);
            proof {
                push_distinct(old_res, x);
            }
        }
    }
    res
}
// </vc-code>

fn main() {}
}