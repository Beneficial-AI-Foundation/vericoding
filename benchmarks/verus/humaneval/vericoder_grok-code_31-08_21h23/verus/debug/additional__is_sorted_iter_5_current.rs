use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>

spec fn sorted_up_to_i(s: Seq<i32>, i: int) -> bool {
    forall |k: int, j: int| 0 <= k < j <= i ==> s@k <= s@j
}

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_sorted(lst: &[i32]) -> (result: bool)
    // pre-conditions-start
    requires
        lst.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <== forall|i: int, j: int| 0 <= i && i < j && j < lst.len() ==> lst[i] <= lst[j],
        !result ==> exists|i: int, j: int| 0 <= i && i < j && j < lst.len() && lst[i] > lst[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = true;
    let mut i: usize = 0;
    let s = lst@;
    let ghost inversion: int = 0;
    while i < lst.len() - 1
        invariant
            0 <= i <= lst.len() - 1,
            forall |k: int, j: int| 0 <= k < j <= i ==> #[trigger] (s@[k] <= s@[j])
    {
        if !(lst[i] <= lst[i + 1]) {
            result = false;
            proof {
                inversion = i as int;
                assert(s@[inversion] > s@[inversion + 1]);
            }
            break;
        }
        i += 1;
    }
    if !result {
        proof {
            assert(0 <= inversion < inversion + 1 < lst.len() && s@[inversion] > s@[inversion + 1]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}