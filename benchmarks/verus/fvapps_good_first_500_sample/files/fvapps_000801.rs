// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
type Interval = (i32, i32);

spec fn unique_chars_in_bytes(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let first = s[0];
        let rest_unique = unique_chars_in_bytes(s.skip(1));
        if s.skip(1).contains(first) {
            rest_unique
        } else {
            rest_unique + 1
        }
    }
}

fn color_intervals(intervals: Vec<Interval>) -> (result: Vec<u8>)
    ensures 
        result.len() == intervals.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            #[trigger] result[i] == 48u8 || #[trigger] result[i] == 49u8
        },
        /* For non-overlapping intervals, at most 2 distinct colors are used */
        intervals.len() >= 2 ==> 
            (forall|i: int, j: int| 0 <= i < intervals.len() && 0 <= j < intervals.len() && i != j ==> {
                let int_i = intervals[i];
                let int_j = intervals[j];
                int_i.0 < int_i.1 && int_j.0 < int_j.1 ==> 
                    (int_i.1 < int_j.0 || int_j.1 < int_i.0)
            }) ==> {
                unique_chars_in_bytes(result@) <= 2
            }
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

fn main() {
    // /* Apps difficulty: interview */
    // /* Assurance level: unguarded */
    // 
    // let test_intervals = vec![(3, 7), (2, 5), (6, 9)];
    // let result = color_intervals(test_intervals);
    // let result_string = String::from_utf8(result).unwrap();
    // println!("{}", result_string); /* Expected: "100" */
}