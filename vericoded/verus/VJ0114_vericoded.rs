// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): spec defining uppercasing of one char */
spec fn to_upper_char_spec(c: char) -> char {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else {
        c
    }
}

/* helper modified by LLM (iteration 3): lemma equating inner_expr_to_uppercase with per-char spec */
proof fn lemma_inner_expr_index(str1: &Vec<char>, i: int)
    requires
        0 <= i < str1.len(),
    ensures
        inner_expr_to_uppercase(str1, i) == to_upper_char_spec(str1[i])
{
    if is_lower_case(str1[i]) {
        assert(inner_expr_to_uppercase(str1, i) == shift_minus_32_spec(str1[i]));
        assert(to_upper_char_spec(str1[i]) == shift_minus_32_spec(str1[i]));
    } else {
        assert(inner_expr_to_uppercase(str1, i) == str1[i]);
        assert(to_upper_char_spec(str1[i]) == str1[i]);
    }
}

/* helper modified by LLM (iteration 3): executable helper matching the spec */
fn to_upper_char(c: char) -> (result: char)
    ensures
        result == to_upper_char_spec(c)
{
    if c >= 'a' && c <= 'z' {
        ((c as u8) - 32) as char
    } else {
        c
    }
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)

    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fix spec indexing to use int and maintain loop invariants */
    let n = str1.len();
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == str1.len(),
            0 <= i as int <= n as int,
            res@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> res@[j] == inner_expr_to_uppercase(str1, j),
        decreases n as int - i as int
    {
        let c = str1[i];
        let u = to_upper_char(c);
        proof {
            lemma_inner_expr_index(str1, i as int);
            assert(u == to_upper_char_spec(str1[i as int]));
            assert(inner_expr_to_uppercase(str1, i as int) == to_upper_char_spec(str1[i as int]));
        }
        res.push(u);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}