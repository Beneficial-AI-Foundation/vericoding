use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_unique_preserved(a: Seq<i32>, i: int, j: int, k: int)
    requires
        forall|p: int, q: int| #![trigger a[p], a[q]] 0 <= p && p < q && q < a.len() ==> a[p] <= a[q],
        0 <= i && i < j && j < k && k < a.len(),
    ensures
        a[i] <= a[k],
{
    if i < k {
        assert(a[i] <= a[k]) by {
            assert(0 <= i && i < k && k < a.len());
        }
    } else {
        assert(a[k] <= a[i]) by {
            assert(0 <= k && k < i && i < a.len());
        }
    }
}

proof fn lemma_strictly_increasing(a: Seq<i32>, result: Seq<i32>)
    requires
        forall|i: int, j: int| #![trigger a[i], a[j]] 0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
        result.len() > 0,
        forall|k: int| 0 <= k && k < result.len() ==> result[k] == a[k as usize],
    ensures
        forall|i: int, j: int| #![trigger result[i], result[j]] 0 <= i && i < j && j < result.len() ==> result[i] < result[j],
{
    assert forall|i: int, j: int| 0 <= i && i < j && j < result.len() implies result[i] < result[j] by {
        assert(result[i] == a[i as usize]);
        assert(result[j] == a[j as usize]);
        if a[i as usize] == a[j as usize] {
            lemma_unique_preserved(a, i, i+1, j);
            assert(a[i as usize] <= a[j as usize]);
            assert(a[i as usize] == a[j as usize]);
        } else {
            assert(a[i as usize] <= a[j as usize]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique_better(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k && k < result.len() ==> result[k] == a[k],
            forall|p: int, q: int| #![trigger result[p], result[q]] 0 <= p && p < q && q < result.len() ==> result[p] < result[q],
    {
        if i == 0 || a[i] > a[i - 1] {
            result.push(a[i]);
        }
        i += 1;
    }
    proof {
        lemma_strictly_increasing(a@, result@);
    }
    result
}
// </vc-code>

fn main() {}
}