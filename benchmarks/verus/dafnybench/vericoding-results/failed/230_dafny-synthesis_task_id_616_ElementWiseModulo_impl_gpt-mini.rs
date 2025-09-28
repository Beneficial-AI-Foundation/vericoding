use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed.
// </vc-helpers>

// <vc-spec>
fn element_wise_modulo(a: &[i32], b: &[i32]) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    let n: int = a.len() as int;
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant { (0 <= i && i <= n) }
        invariant { ((result.len() as int) == i) }
        invariant { forall|j: int| (0 <= j && j < i) ==> (result[j as usize] == a[j as usize] % b[j as usize]) }
        decreases { n - i }
    {
        assert(0 <= i && i < n);
        assert(a.len() == b.len());
        assert(n == b.len() as int);
        assert(b[i as usize] != 0);
        let val: i32 = a[i as usize] % b[i as usize];
        result.push(val);
        i = i + 1;
    }
    // From the loop invariants and loop exit condition we can conclude the postconditions.
    assert(i == n);
    assert((result.len() as int) == n);
    assert(result.len() == a.len());
    assert(forall|j: int| (0 <= j && j < result.len() as int) ==> (result[j as usize] == a[j as usize] % b[j as usize]));
    result
}
// </vc-code>

fn main() {
}

}