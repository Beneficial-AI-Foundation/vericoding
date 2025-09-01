use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut result = Vec::<i32>::new();
    let mut i: usize = 0;
    while i < l.len()
        invariant
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == l@[j] + 1,
        decreases l.len() as int - i as int,
    {
        proof {
            assert(0 <= i as int < l.len() as int);
            assert(l@[i] + 1 <= i32::MAX);
            assert(l@[i] <= i32::MAX - 1);
        }
        let val = l[i];
        result.push(val + 1);
        i += 1;
    }
    proof {
        assert(result.len() as int == i as int);
        assert(i as int == l.len() as int);
        assert(result.len() as int == l.len() as int);
    }
    result
}
// </vc-code>
// </vc-code>

fn main() {}
}