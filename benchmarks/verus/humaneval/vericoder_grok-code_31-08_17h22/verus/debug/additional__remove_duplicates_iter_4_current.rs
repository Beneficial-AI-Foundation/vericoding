use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>

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
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| #![auto] 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() <= a.len(),
            forall |j: int, k: int| 0 <= j < k < res.len() ==> res@[j] != res@[k],
            forall |j: int| 0 <= j < res.len() ==> #[trigger] exists |k: int| 0 <= k < i as int ==> a@[k] == res@[j],
        decreases a.len() - i
    {
        let elem = a[i];
        if !res.contains(&elem) {
            res.push(elem);
        }
        i += 1;
    }
    proof {
        assert(forall|i: int| 0 <= i < res.len() ==> in_array(a@, res@[i]));
        assert(forall|i: int, j: int| 0 <= i < j < res.len() ==> res@[i] != res@[j]);
    };
    res
}
// </vc-code>

fn main() {}
}