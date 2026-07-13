// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn starts_with_q(s: Seq<char>) -> bool {
    s.len() > 0 && s[0] == 'Q'
}

spec fn count_query_ops(ops: Seq<Seq<char>>) -> nat
    decreases ops.len()
{
    if ops.len() == 0 {
        0
    } else {
        let rest_count = count_query_ops(ops.skip(1));
        if starts_with_q(ops[0]) {
            rest_count + 1
        } else {
            rest_count
        }
    }
}

fn fenwick_operations(n: u32, m: u32, c: i64, ops: Vec<String>) -> (results: Vec<i64>)
    requires 
        n > 0,
        m >= 0,
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
    // let test_result = fenwick_operations(7, 5, 0, vec!["Q 7".to_string(), "S 1 7 1".to_string(), "Q 3".to_string(), "S 1 3 1".to_string(), "Q 3".to_string()]);
    // println!("{:?}", test_result);
}