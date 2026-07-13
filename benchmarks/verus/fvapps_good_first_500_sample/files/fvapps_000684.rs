// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn string_to_int(s: Seq<char>) -> int
{
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        if s[0] == '0' { 0 }
        else if s[0] == '1' { 1 }
        else if s[0] == '2' { 2 }
        else if s[0] == '3' { 3 }
        else if s[0] == '4' { 4 }
        else if s[0] == '5' { 5 }
        else if s[0] == '6' { 6 }
        else if s[0] == '7' { 7 }
        else if s[0] == '8' { 8 }
        else if s[0] == '9' { 9 }
        else { 0 }
    } else {
        10 * string_to_int(s.drop_last()) + string_to_int(s.last(1))
    }
}
// </vc-helpers>

// <vc-spec>
fn consecutive_sum(arr: Vec<i32>) -> (result: Vec<String>)
    requires arr.len() >= 3,
    ensures 
        result.len() == arr.len() - 2,
        forall|i: int| 0 <= i < result.len() ==> result[i]@.len() >= 1,
        forall|i: int| 0 <= i < result.len() ==> {
            let sum_val = arr[i] + arr[i + 1] + arr[i + 2];
            string_to_int(result[i]@) == sum_val
        },
        forall|i: int| 0 <= i < result.len() ==> {
            let min_val = if arr[i] <= arr[i + 1] && arr[i] <= arr[i + 2] { arr[i] }
                         else if arr[i + 1] <= arr[i + 2] { arr[i + 1] }
                         else { arr[i + 2] };
            string_to_int(result[i]@) >= min_val
        },
        (forall|x: i32| arr@.contains(x) ==> x == 0) ==> 
            (forall|i: int| 0 <= i < result.len() ==> result[i]@ == "0"@)
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