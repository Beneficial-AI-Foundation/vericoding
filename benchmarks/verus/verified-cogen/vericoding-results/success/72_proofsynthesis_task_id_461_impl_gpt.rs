// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    (c as u32) >= 97 && (c as u32) <= 122
}

spec fn is_upper_case(c: char) -> (result: bool) {
    (c as u32) >= 65 && (c as u32) <= 90
}

spec fn count_uppercase_recursively(seq: Seq<char>) -> (result: int)
    decreases seq.len(),
{
    if seq.len() == 0 {
        0
    } else {
        count_uppercase_recursively(seq.drop_last()) + if is_upper_case(seq.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added executable uppercase check and usize-counting helper with proper specs and inductive proof links */
fn is_upper_case_exec(c: char) -> (b: bool)
    ensures
        b == is_upper_case(c),
{
    let cu = c as u32;
    cu >= 65 && cu <= 90
}

fn count_uppercase_upto(text: &Vec<char>, n: usize) -> (count: usize)
    requires
        n <= text.len(),
    ensures
        0 <= count@ <= n as int,
        count_uppercase_recursively(text@.take(n as int)) == count@,
    decreases n
{
    if n == 0 {
        0usize
    } else {
        let prev = count_uppercase_upto(text, n - 1);
        let c = text[n - 1];
        let inc: usize = if is_upper_case_exec(c) { 1 } else { 0 };
        let res = prev + inc;
        proof {
            assert(text@.take(n as int).drop_last() == text@.take((n - 1) as int));
            assert(text@.take(n as int).len() == n as int);
            assert(text@.take(n as int).last() == text@[((n - 1) as int)]);
            assert(c == text@[((n - 1) as int)]);
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
fn count_uppercase(text: &Vec<char>) -> (count: u64)

    ensures
        0 <= count <= text.len(),
        count_uppercase_recursively(text@) == count,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Use usize helper, prove correspondence, and cast to u64 */
    let n = text.len();
    let acc: usize = count_uppercase_upto(text, n);
    proof {
        assert(text@.take(n as int) == text@);
        assert(0 <= acc@ && acc@ <= n as int);
    }
    acc as u64
}
// </vc-code>

}
fn main() {}