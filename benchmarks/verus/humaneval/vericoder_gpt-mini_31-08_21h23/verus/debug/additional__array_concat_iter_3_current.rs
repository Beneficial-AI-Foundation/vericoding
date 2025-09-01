use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// No helpers needed.
 // </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let alen: int = a.len() as int;
    let blen: int = b.len() as int;

    let mut res: Vec<i32> = Vec::new();

    // First loop: copy a
    let mut i: int = 0;
    while i < alen {
        invariant i >= 0 && i <= alen;
        invariant res.len() == (i as usize);
        invariant forall|j: int| 0 <= j && j < i ==>
            res[j as usize] == a[j as usize];
        decreases alen - i;
        let v = a[i as usize];
        res.push(v);
        i += 1;
    }

    // After first loop, res.len() == alen and prefix equal to a
    assert(res.len() == (alen as usize));
    assert(forall|j: int| 0 <= j && j < alen ==> res[j as usize] == a[j as usize]);

    // Second loop: copy b
    let mut k: int = 0;
    while k < blen {
        invariant k >= 0 && k <= blen;
        invariant res.len() == ((alen + k) as usize);
        invariant forall|j: int| 0 <= j && j < alen ==>
            res[j as usize] == a[j as usize];
        invariant forall|j: int| 0 <= j && j < k ==>
            res[(alen + j) as usize] == b[j as usize];
        decreases blen - k;
        let v = b[k as usize];
        res.push(v);
        k += 1;
    }

    // Final assertions matching ensures
    assert(res.len() == ((alen + blen) as usize));
    assert(forall|j: int| 0 <= j && j < alen ==> res[j as usize] == a[j as usize]);
    assert(forall|j: int| 0 <= j && j < blen ==> res[(alen + j) as usize] == b[j as usize]);

    res
    // impl-end
}
// </vc-code>

fn main() {}
}