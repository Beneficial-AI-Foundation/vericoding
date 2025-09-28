// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_value(o: Option<int>) -> int
    recommends o.is_Some()
{
    o.get_Some_0()
}
// </vc-preamble>

// <vc-helpers>
fn min_i8(a: i8, b: i8) -> (res: i8)
    ensures
        res == a || res == b,
        res <= a,
        res <= b,
{
    if a < b { a } else { b }
}

fn max_i8(a: i8, b: i8) -> (res: i8)
    ensures
        res == a || res == b,
        res >= a,
        res >= b,
{
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: Vec<i8>) -> (result: (Option<i8>, Option<i8>))
// </vc-spec>
// <vc-code>
{
    if arr.len() == 0 {
        return (Option::None, Option::None);
    }

    let mut smallest = arr[0];
    let mut largest = arr[0];
    let mut i: usize = 1;

    while i < arr.len()
        invariant
            arr.len() > 0,
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> smallest <= arr@[k],
            exists|k: int| 0 <= k < i && smallest == arr@[k],
            forall|k: int| 0 <= k < i ==> largest >= arr@[k],
            exists|k: int| 0 <= k < i && largest == arr@[k],
        decreases arr.len() - i
    {
        smallest = min_i8(smallest, arr[i]);
        largest = max_i8(largest, arr[i]);
        i = i + 1;
    }

    (Option::Some(smallest), Option::Some(largest))
}
// </vc-code>


}

fn main() {}