// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'x' || s[i] == 'y'
}

spec fn count_char(s: Seq<char>, c: char) -> nat {
    s.filter(|x: char| x == c).len()
}

spec fn valid_output(s: Seq<char>, result: Seq<char>) -> bool 
    recommends valid_input(s)
{
    let count_x = count_char(s, 'x');
    let count_y = count_char(s, 'y');
    if count_y > count_x {
        result.len() == count_y - count_x && forall|i: int| 0 <= i < result.len() ==> result[i] == 'y'
    } else {
        result.len() == count_x - count_y && forall|i: int| 0 <= i < result.len() ==> result[i] == 'x'
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by removing `auto` from `lemma auto fn` and simplifying the `ensures` clause for clarity and readability without changing its logical meaning. */

lemma fn lemma_abs_diff(a: int, b: int) ensures ((a - b).abs() == if a > b { a - b } else { b - a }) { 
    if a > b {
        assert((a - b).abs() == a - b);
    } else {
        assert((a - b).abs() == b - a);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_input(s@)
    ensures valid_output(s@, result@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added explicit proof `lemma_abs_diff` call for `count_to_add` derivation, and fixed issues related to `nat` and `int` type conversions. */
{
    let mut x_count: nat = 0;
    let mut y_count: nat = 0;

    let mut i: nat = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            x_count == count_char(s@.subsequence(0, i as int), 'x'),
            y_count == count_char(s@.subsequence(0, i as int), 'y'),
            valid_input(s@)
        decreases s.len() - i
    {
        if s[i] == 'x' {
            x_count = x_count + 1;
        } else {
            y_count = y_count + 1;
        }
        i = i + 1;
    }

    let mut result_vec: Vec<char> = Vec::new();
    let target_char: char;
    let count_to_add_int: int;

    proof {
        lemma_abs_diff(x_count as int, y_count as int);
    }

    if y_count > x_count {
        target_char = 'y';
        count_to_add_int = y_count as int - x_count as int;
    } else {
        target_char = 'x';
        count_to_add_int = x_count as int - y_count as int;
    }
    let count_to_add = count_to_add_int as nat;

    proof {
        assert(count_char(s@, 'x') == x_count);
        assert(count_char(s@, 'y') == y_count);
    }

    let mut k: nat = 0;
    while k < count_to_add
        invariant
            0 <= k <= count_to_add,
            result_vec@.len() == k,
            forall|idx: int| 0 <= idx < k ==> result_vec@[idx] == target_char,
            count_char(s@, 'x') == x_count, // preserve counts from earlier loop
            count_char(s@, 'y') == y_count,
        decreases count_to_add - k
    {
        result_vec.push(target_char);
        k = k + 1;
    }

    result_vec
}
// </vc-code>


}

fn main() {}