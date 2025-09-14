// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn le_trans_i32(a: i32, b: i32, c: i32)
    ensures (a <= b && b <= c) ==> a <= c
{ }

proof fn le_total_i32(a: i32, b: i32)
    ensures a <= b || b <= a
{ }
// </vc-helpers>

// <vc-spec>
fn min_second_value_first(arr: &Vec<Vec<i32>>) -> (first_of_min_second: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() >= 2,

    ensures
        exists|i: int|
            0 <= i < arr.len() && first_of_min_second == #[trigger] arr[i][0] && (forall|j: int|
                0 <= j < arr.len() ==> (arr[i][1] <= #[trigger] arr[j][1])),
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    assert(n > 0);
    assert(arr[0].len() >= 2);

    let mut min_i: usize = 0;
    let mut i: usize = 1;
    while i < n
        invariant 1 <= i && i <= n
        invariant 0 <= min_i && min_i < i
        invariant arr[min_i].len() >= 2
        invariant forall|j: int| 0 <= j && j < i as int ==> arr[min_i][1] <= arr[j as usize][1]
    {
        assert(0 <= i as int && i as int < n as int);
        assert(0 <= min_i as int && min_i as int < n as int);
        assert(arr[i].len() >= 2);
        assert(arr[min_i].len() >= 2);

        if arr[i][1] < arr[min_i][1] {
            min_i = i;
        }
        i = i + 1;
    }
    let first_of_min_second = arr[min_i][0];
    first_of_min_second
}
// </vc-code>

}
fn main() {}