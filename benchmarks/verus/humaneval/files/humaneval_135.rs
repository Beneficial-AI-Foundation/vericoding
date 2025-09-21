// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j]
}

spec fn has_decrease_at(arr: Seq<int>, i: int) -> bool {
    1 <= i < arr.len() && arr[i] < arr[i-1]
}

spec fn is_largest_decrease_index(arr: Seq<int>, result: int) -> bool {
    has_decrease_at(arr, result) && 
    (forall|j: int| result < j < arr.len() ==> #[trigger] arr[j] >= arr[j-1])
}

spec fn is_non_decreasing(arr: Seq<int>) -> bool {
    forall|i: int| 1 <= i < arr.len() ==> #[trigger] arr[i] >= arr[i-1]
}

spec fn seq_map_to_int(arr: Seq<i8>) -> Seq<int> {
    arr.map(|_i: int, x: i8| x as int)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn can_arrange(arr: Vec<i8>) -> (result: i8)
  requires 
      valid_input(seq_map_to_int(arr@)),
  ensures 
      (result == -1) || (0 < result as int && (result as int) < (arr@.len() as int)),
      result == -1 ==> is_non_decreasing(seq_map_to_int(arr@)),
      result != -1 ==> is_largest_decrease_index(seq_map_to_int(arr@), result as int),
      result != -1 ==> (exists|i: int| has_decrease_at(seq_map_to_int(arr@), i))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}