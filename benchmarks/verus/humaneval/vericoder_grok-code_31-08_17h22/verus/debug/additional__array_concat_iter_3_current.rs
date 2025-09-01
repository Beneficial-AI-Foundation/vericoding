use vstd::prelude::*;

verus! {

// <vc-helpers>

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
#[verifier::loop_isolation_folder(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == (a.len() as int) + (b.len() as int),
        forall|i: int| #![trigger] 0 <= i && i < a.len() as int ==> result[i] == a[i as usize],
        forall|i: int| #![trigger] 0 <= i && i < b.len() as int ==> result[i + (a.len() as int)] == b[i as usize],
    // post-conditions-end
{
    let mut result = Vec::<i32>::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == (i as int),
            forall|k: int| #![trigger] 0 <= k && k < i ==> result[k as usize] == a[k as usize],
            i <= a.len(),
        decreases
            a.len() as int - i as int,
    {
        result.push(a[i]);
        i += 1;
    }
    let mut j = 0;
    while j < b.len()
        invariant
            result.len() == (a.len() as int + j as int),
            forall|k: int| #![trigger] 0 <= k && k < a.len() as int ==> result[k as usize] == a[k as usize],
            forall|k: int| #![trigger] 0 <= k && k < j ==> result[((a.len() as int) + k) as usize] == b[k as usize],
            j <= b.len(),
        decreases
            b.len() as int - j as int,
    {
        result.push(b[j]);
        j += 1;
    }
    assert(forall|i: int| #![trigger] i >= 0 && i < b.len() as int ==> result[(i + (a.len() as int)) as usize] == b[i as usize]) by {
        assert(j == b.len()) by { };
    };
    result
}
// </vc-code>

fn main() {}
}