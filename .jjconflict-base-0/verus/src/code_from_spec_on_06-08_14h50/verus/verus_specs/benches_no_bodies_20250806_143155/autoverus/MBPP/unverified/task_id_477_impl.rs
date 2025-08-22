use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_upper_case(c: u8) -> bool {
    c >= 65 && c <= 90
}

spec fn shift32_spec(c: u8) -> u8 {
    (c + 32) as u8
}

fn to_lowercase(str1: &[u8]) -> (result: Vec<u8>)
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
{
    let mut lower_case: Vec<u8> = Vec::with_capacity(str1.len());
    let mut index = 0;
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while index < str1.len()
        invariant
            0 <= index <= str1.len(),
            lower_case.len() == index,
            forall|i: int| 0 <= i < index ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
        decreases str1.len() - index
    {
        if (str1[index] >= 65 && str1[index] <= 90) {
            lower_case.push((str1[index] + 32) as u8);
        } else {
            lower_case.push(str1[index]);
        }
        index += 1;
    }
    lower_case
}

} // verus!