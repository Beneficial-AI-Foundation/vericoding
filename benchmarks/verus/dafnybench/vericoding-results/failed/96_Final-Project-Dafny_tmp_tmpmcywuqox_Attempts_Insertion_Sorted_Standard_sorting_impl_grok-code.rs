use vstd::prelude::*;

verus! {

spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

// <vc-helpers>
spec fn insertion_sorted(array: Seq<int>, left: int, right: int) -> bool
    recommends 0 <= left <= right <= array.len()
{
    forall|i: int, j: int| left <= i < j < right ==> array[i] <= array[j]
}

spec fn sorted_up_to(s: Seq<int>, k: int) -> bool
{
    insertion_sorted(s, 0, k)
}
// </vc-helpers>

// <vc-spec>
fn sorting(array: &mut Vec<int>)
    requires old(array).len() > 1
    ensures insertion_sorted(array@, 0, array@.len() as int)
// </vc-spec>
// <vc-code>
{
    let n = array.len();
    let mut i = 1;

    while i < n
        invariant
            1 <= i <= n,
            sorted_up_to(array@, i as int),
        decreases n - i
    {
        let mut j = i;

        while j > 0
            invariant
                1 <= i < n,
                0 <= j <= i,
                sorted_up_to(array@, i as int),
                forall|k: int| 0 <= k < (j as int) ==> array@[k] <= array@[k + 1],
            decreases j
        {
            if array[j - 1] > array[j] {
                let temp = array[j];
                array[j] = array[j - 1];
                array[j - 1] = temp;
            } else {
                break;
            }
            j -= 1;
        }

        proof {
            assert(sorted_up_to(array@, (i as int) + 1));
        }

        i += 1;
    }
}
// </vc-code>

fn main() {}

}