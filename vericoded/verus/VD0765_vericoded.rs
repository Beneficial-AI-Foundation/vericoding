use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn remove_element(s: &Vec<i32>, k: usize) -> (v: Vec<i32>)
    requires 
        k < s.len(),
    ensures
        v.len() == s.len() - 1,
        forall|i: int| 0 <= i < k ==> v[i] == s[i],
        forall|i: int| k <= i < v.len() ==> v[i] == s[(i + 1) as int],
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();

    // Copy elements before k
    let mut i: usize = 0;
    while i < k
        invariant
            (i as int) <= s.len(),
            (k as int) <= s.len(),
            i <= k,
            res.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> #[trigger] res@[j] == s@[j],
        decreases (k as int) - (i as int)
    {
        assert(i < s.len());
        res.push(s[i]);
        i += 1;
    }

    assert(i == k);
    // Skip element at k and continue with the rest
    i += 1;

    while i < s.len()
        invariant
            (i as int) <= s.len(),
            i > k,
            res.len() == (i as int) - 1,
            forall|j: int| 0 <= j && j < k as int ==> #[trigger] res@[j] == s@[j],
            forall|j: int| k as int <= j && j < res.len() ==> #[trigger] res@[j] == s@[(j + 1) as int],
        decreases s.len() - (i as int)
    {
        assert(i < s.len());
        res.push(s[i]);
        i += 1;
    }

    res
}
// </vc-code>

fn main() {}
}