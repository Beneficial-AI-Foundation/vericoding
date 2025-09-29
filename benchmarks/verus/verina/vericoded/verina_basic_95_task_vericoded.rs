// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn dummy() { }
// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
// </vc-spec>
// <vc-code>
{
    let mut r = arr.clone();
    let ai = arr[i];
    let aj = arr[j];

    proof {
        assert(r.len() == arr.len());
    }

    r.set(i, aj);

    let r1 = Ghost(r@);
    proof {
        assert(r1@[i as int] == arr@[j as int]);
        assert(forall|k: int|
            0 <= k < arr.len() && k != i ==> #[trigger] r1@[k] == arr@[k]
        );
    }

    r.set(j, ai);

    proof {
        assert(r.len() == arr.len());
        if i == j {
            assert(arr@[i as int] == arr@[j as int]);
            assert(r@[i as int] == arr@[j as int]);
            assert(r@[j as int] == arr@[i as int]);
            assert(forall|k: int|
                0 <= k < arr.len() && k != i && k != j ==> #[trigger] r@[k] == arr@[k]
            );
        } else {
            assert(r@[i as int] == r1@[i as int]);
            assert(r1@[i as int] == arr@[j as int]);
            assert(r@[j as int] == ai);
            assert(ai == arr@[i as int]);
            assert(forall|k: int|
                0 <= k < arr.len() && k != i && k != j ==> #[trigger] r@[k] == r1@[k]
            );
            assert(forall|k: int|
                0 <= k < arr.len() && k != i ==> #[trigger] r1@[k] == arr@[k]
            );
            assert(forall|k: int|
                0 <= k < arr.len() && k != i && k != j ==> #[trigger] r@[k] == arr@[k]
            );
        }
    }

    r
}
// </vc-code>

}
fn main() {}