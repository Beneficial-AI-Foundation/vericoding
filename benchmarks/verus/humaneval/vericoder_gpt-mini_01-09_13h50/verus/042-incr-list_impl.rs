use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
// Updated helpers: none required for this proof, but keep the section for potential future use.
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn incr_list(l: Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        forall|i: int| 0 <= i < l.len() ==> l[i] + 1 <= i32::MAX,
    // pre-conditions-end

    // post-conditions-start
    ensures
        result.len() == l.len(),
        forall|i: int| 0 <= i < l.len() ==> #[trigger] result[i] == l[i] + 1,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    let n: int = l.len() as int;
    while i < n
        invariant {
            0 <= i && i <= n;
            res.len() as int == i;
            forall |j: int| 0 <= j && j < i ==> res[j as usize] == l[j as usize] + 1;
        }
        decreases n - i;
    {
        // safe by precondition: for this i, l[i as usize] + 1 <= i32::MAX
        res.push(l[i as usize] + 1);
        i = i + 1;
    }
    proof {
        assert(i == n);
        assert(res.len() as int == n);
        assert(forall |k: int| 0 <= k && k < n ==> res[k as usize] == l[k as usize] + 1);
        assert(forall |k: int| 0 <= k && k < l.len() as int ==>
            res[k as usize] == l[k as usize] + 1);
    }
    res
}
// </vc-code>

fn main() {}
}