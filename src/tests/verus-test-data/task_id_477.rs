use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> (result:bool) {
    c >= 'A' && c <= 'Z'
}
// pure-end

spec fn shift32_spec(c: char) -> (result:char) {
    ((c as u8) + 32) as char
}
// pure-end

fn to_lowercase(str1: &Vec<char>) -> (result: Vec<char>)
    // post-conditions-start
    ensures
        str1@.len() == result@.len(),
        forall|i: int|
            0 <= i < str1.len() ==> result[i] == (if is_upper_case(#[trigger] str1[i]) {
                shift32_spec(str1[i])
            } else {
                str1[i]
            }),
    // post-conditions-end
{
    // impl-start
    let mut lower_case: Vec<char> = Vec::with_capacity(str1.len());
    let mut index = 0;
    while index < str1.len()
        // invariants-start
        invariant
            0 <= index <= str1.len(),
            lower_case.len() == index,
            forall|i: int|
                0 <= i < index ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
                    shift32_spec(str1[i])
                } else {
                    str1[i]
                }),
        // invariants-end
    {
        if (str1[index] >= 'A' && str1[index] <= 'Z') {
            lower_case.push(((str1[index] as u8) + 32) as char);
        } else {
            lower_case.push(str1[index]);
        }
        // assert-start
        assert(lower_case[index as int] == (if is_upper_case(str1[index as int]) {
            shift32_spec(str1[index as int])
        } else {
            str1[index as int]
        }));
        // assert-end
        index += 1;
    }
    // assert-start
    assert(forall|i: int|
        0 <= i < str1.len() ==> lower_case[i] == (if is_upper_case(#[trigger] str1[i]) {
            shift32_spec(str1[i])
        } else {
            str1[i]
        }));
    // assert-end
    lower_case
    // impl-end
}

} // verus!

fn main() {}
