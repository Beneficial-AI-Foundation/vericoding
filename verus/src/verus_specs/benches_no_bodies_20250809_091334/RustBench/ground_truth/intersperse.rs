use vstd::prelude::*;

verus! {

fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

fn main() {}
}
