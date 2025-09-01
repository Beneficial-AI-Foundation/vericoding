use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end
// pure-end

spec fn is_lower_case(c: char) -> (result:bool) {
    c >= 'a' && c <= 'z'
}
// pure-end
// pure-end

spec fn shift_plus_32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end
// pure-end

spec fn shift_minus_32_spec(c: char) -> (result:char) {
    ((c as u8) - 32) as char
}
// pure-end
// pure-end

spec fn flip_case_spec(c: char) -> (result:char) {
    if is_lower_case(c) {
        shift_minus_32_spec(c)
    } else if is_upper_case(c) {
        shift_plus_32_spec(c)
    } else {
        c
    }
}
// pure-end

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn flip_case(str: &[char]) -> (flipped_case: Vec<char>)
    // post-conditions-start
    ensures
        str@.len() == flipped_case@.len(),
        forall|i: int| 0 <= i < str.len() ==> flipped_case[i] == flip_case_spec(#[trigger] str[i]),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n: int = str.len() as int;
    let mut res: Vec<char> = Vec::new();
    let mut i: int = 0;
    while (i < n)
        invariant i >= 0;
        invariant i <= n;
        invariant res@.len() as int == i;
        invariant forall |j: int| 0 <= j < i ==> res@[j] == flip_case_spec(#[trigger] str@[j]);
        decreases n - i;
    {
        let c: char = str[i as usize];
        let fc: char = if c >= 'a' && c <= 'z' {
            ((c as u8) - 32) as char
        } else if c >= 'A' && c <= 'Z' {
            ((c as u8) + 32) as char
        } else {
            c
        };
        proof {
            assert(fc == flip_case_spec(#[trigger] c));
        }
        res.push(fc);
        proof {
            assert(res[i as usize] == fc);
            assert(res@[i] == fc);
            assert(res@[i] == flip_case_spec(#[trigger] c));
        }
        i += 1;
    }
    res
}
// </vc-code>

} // verus!
fn main() {}