use vstd::prelude::*;

verus! {

spec fn in_array(a: &[i32], x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn count_in_vec(v: &Vec<i32>, x: i32) -> nat {
    let mut count = 0;
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            count == count_up_to(v, x, i)
    {
        if v@[i] == x {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}

spec fn count_up_to(v: &Vec<i32>, x: i32, up_to: nat) -> nat {
    let mut c = 0;
    let mut j = 0;
    while j < up_to
        invariant
            0 <= j <= up_to,
            c == if j == 0 { 0 } else { count_up_to(v, x, j - 1) + if v@[j - 1] == x { 1 } else { 0 } }
    {
        if v@[j] == x {
            c = c + 1;
        }
        j = j + 1;
    }
    c
}

proof fn vec_contains_implies_in_array(a: &[i32], v: &Vec<i32>, x: i32)
    requires
        v@.contains(x),
    ensures
        in_array(a, x),
{
    let i = choose|i: int| 0 <= i < v.len() && v@[i] == x;
    assert(0 <= i < v.len() && v@[i] == x);
    assert(0 <= i < a.len() && a[i] == x) by {
        assert(a.len() == v.len());
        assert(forall|j: int| 0 <= j < v.len() ==> a[j] == v@[j]);
    };
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn shared_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        // All elements in the output are in both a and b
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        // The elements in the output are all different
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j]
// </vc-spec>
// </vc-spec>

// <vc-code>
fn shared_elements(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    ensures
        forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result@[i] != result@[j]
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|x: i32| result@.contains(x) ==> (in_array(a, x) && in_array(b, x)),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result@[k] != result@[l]
    {
        let x = a[i];
        if in_array(b, x) && !result@.contains(x) {
            result.push(x);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

fn main() {
}

}