// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(arr: Seq<int>) -> bool {
    forall|i: int| 0 <= i < arr.len() ==> arr[i] >= 0
}

spec fn has_even_value(arr: Seq<int>) -> bool {
    exists|i: int| 0 <= i < arr.len() && arr[i] % 2 == 0
}

spec fn smallest_even_value(arr: Seq<int>) -> int {
    smallest_even_value_helper(arr, 0, -1)
}

spec fn smallest_even_value_helper(arr: Seq<int>, index: int, current_min: int) -> int
    decreases arr.len() - index
{
    if index >= arr.len() {
        current_min
    } else if arr[index] % 2 == 0 {
        if current_min == -1 || arr[index] < current_min {
            smallest_even_value_helper(arr, index + 1, arr[index])
        } else {
            smallest_even_value_helper(arr, index + 1, current_min)
        }
    } else {
        smallest_even_value_helper(arr, index + 1, current_min)
    }
}

spec fn first_index_of_value(arr: Seq<int>, value: int) -> int
    decreases arr.len()
{
    if arr.len() > 0 && arr[0] == value {
        0
    } else if arr.len() > 0 {
        1 + first_index_of_value(arr.subrange(1, arr.len() as int), value)
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): simple evenness predicate reused in specs */
spec fn is_even(x: int) -> bool {
    x % 2 == 0
}

// </vc-helpers>

// <vc-spec>
fn pluck(arr: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(arr@.map_values(|x: i8| x as int))
    ensures 
        arr@.len() == 0 ==> result@.len() == 0,
        !has_even_value(arr@.map_values(|x: i8| x as int)) ==> result@.len() == 0,
        has_even_value(arr@.map_values(|x: i8| x as int)) ==> result@.len() == 2,
        result@.len() == 2 ==> (0 <= (result@[1] as int) && (result@[1] as int) < (arr@.len() as int)),
        result@.len() == 2 ==> arr@[result@[1] as int] as int == result@[0] as int,
        result@.len() == 2 ==> result@[0] as int % 2 == 0,
        result@.len() == 2 ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 ==> result@[0] as int <= arr@[i] as int,
        result@.len() == 2 ==> forall|i: int| 0 <= i < arr@.len() && arr@[i] as int % 2 == 0 && arr@[i] as int == result@[0] as int ==> result@[1] as int <= i
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed invariant casts and maintained linear scan for smallest even with earliest index */
    let n: usize = arr.len();
    let mut i: usize = 0;
    let mut found: bool = false;
    let mut min_val: i8 = 0;
    let mut min_idx: usize = 0;

    while i < n
        invariant
            arr@ == old(arr@),
            0 <= (i as int) && (i as int) <= (n as int),
            (!found) ==> forall|j: int| 0 <= j && j < (i as int) ==> (arr@[j] as int) % 2 != 0,
            found ==> 0 <= (min_idx as int) && (min_idx as int) < (i as int),
            found ==> arr@[(min_idx as int)] as int == (min_val as int),
            found ==> (min_val as int) % 2 == 0,
            found ==> forall|j: int| 0 <= j && j < (i as int) && (arr@[j] as int) % 2 == 0 ==> (min_val as int) <= arr@[j] as int,
            found ==> forall|j: int| 0 <= j && j < (i as int) && arr@[j] as int % 2 == 0 && arr@[j] as int == (min_val as int) ==> (min_idx as int) <= j,
        decreases (n as int) - (i as int)
    {
        let ai: i8 = arr[i];
        if ai % 2 == 0 {
            if !found {
                found = true;
                min_val = ai;
                min_idx = i;
            } else {
                if (ai as int) < (min_val as int) {
                    min_val = ai;
                    min_idx = i;
                } else if (ai as int) == (min_val as int) {
                    // keep earliest index
                } else {
                    // keep previous min
                }
            }
        }
        i = i + 1;
    }

    if !found {
        Vec::new()
    } else {
        let mut out: Vec<i8> = Vec::new();
        out.push(min_val);
        out.push(min_idx as i8);
        out
    }
}
// </vc-code>


}

fn main() {}