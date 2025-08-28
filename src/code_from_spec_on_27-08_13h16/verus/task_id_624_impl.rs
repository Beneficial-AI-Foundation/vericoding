use vstd::prelude::*;

verus! {

spec fn is_lower_case(c: char) -> (result: bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result: char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn inner_expr_to_uppercase(str1: &Vec<char>, i: int) -> (result:char) {
    if is_lower_case(#[trigger] str1[i]) {
        shift_minus_32_spec(str1[i])
    } else {
        str1[i]
    }
}

// <vc-helpers>
spec fn seq_to_uppercase(s: Seq<char>, i: int) -> char
    decreases s.len() - i
{
    if i >= s.len() {
        ' '
    } else if is_lower_case(s[i]) {
        shift_minus_32_spec(s[i])
    } else {
        s[i]
    }
}
// </vc-helpers>

// <vc-spec>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result[i] == (inner_expr_to_uppercase(str1, i))),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn to_uppercase(str1: &Vec<char>) -> (result: Vec<char>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> (result@[i] == (inner_expr_to_uppercase(str1, i))),
{
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;

    while i < str1.len()
        invariant
            i <= str1.len(),
            res@.len() == i,
            forall|k: int| 0 <= k < i ==> res@[k] == inner_expr_to_uppercase(str1, k),
    {
        let c = str1@[i];
        if is_lower_case(c) {
            res.push(shift_minus_32_spec(c));
        } else {
            res.push(c);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

} // verus!

fn main() {}