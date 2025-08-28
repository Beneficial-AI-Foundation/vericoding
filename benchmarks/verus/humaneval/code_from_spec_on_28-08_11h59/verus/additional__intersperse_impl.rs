use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn intersperse_spec(numbers: Seq<i32>, delim: i32) -> Seq<i32>
    decreases numbers.len()
{
    if numbers.len() == 0 {
        seq![]
    } else if numbers.len() == 1 {
        seq![numbers[0]]
    } else {
        seq![numbers[0], delim] + intersperse_spec(numbers.subrange(1, numbers.len() as int), delim)
    }
}

proof fn intersperse_spec_len(numbers: Seq<i32>, delim: i32)
    ensures
        numbers.len() == 0 ==> intersperse_spec(numbers, delim).len() == 0,
        numbers.len() != 0 ==> intersperse_spec(numbers, delim).len() == 2 * numbers.len() - 1
    decreases numbers.len()
{
    if numbers.len() == 0 {
    } else if numbers.len() == 1 {
    } else {
        intersperse_spec_len(numbers.subrange(1, numbers.len() as int), delim);
    }
}

proof fn intersperse_spec_even(numbers: Seq<i32>, delim: i32, i: int)
    requires 
        0 <= i && i < intersperse_spec(numbers, delim).len() && i % 2 == 0,
        numbers.len() > 0
    ensures intersperse_spec(numbers, delim)[i] == numbers[i / 2]
    decreases numbers.len()
{
    if numbers.len() == 1 {
        assert(i == 0);
        assert(intersperse_spec(numbers, delim) == seq![numbers[0]]);
    } else {
        if i == 0 {
            assert(intersperse_spec(numbers, delim)[0] == numbers[0]);
        } else {
            let sub_seq = numbers.subrange(1, numbers.len() as int);
            assert(i >= 2);
            assert(i - 2 >= 0);
            intersperse_spec_len(sub_seq, delim);
            assert((i - 2) < intersperse_spec(sub_seq, delim).len());
            intersperse_spec_even(sub_seq, delim, i - 2);
            assert(intersperse_spec(sub_seq, delim)[i - 2] == sub_seq[(i - 2) / 2]);
            assert(sub_seq[(i - 2) / 2] == numbers[1 + (i - 2) / 2]);
            assert(1 + (i - 2) / 2 == i / 2);
            assert(intersperse_spec(numbers, delim)[i] == intersperse_spec(sub_seq, delim)[i - 2]);
        }
    }
}

proof fn intersperse_spec_odd(numbers: Seq<i32>, delim: i32, i: int)
    requires 
        0 <= i && i < intersperse_spec(numbers, delim).len() && i % 2 == 1,
        numbers.len() > 1
    ensures intersperse_spec(numbers, delim)[i] == delim
    decreases numbers.len()
{
    if i == 1 {
        assert(intersperse_spec(numbers, delim)[1] == delim);
    } else {
        let sub_seq = numbers.subrange(1, numbers.len() as int);
        assert(i >= 3);
        assert(i - 2 >= 1);
        intersperse_spec_len(sub_seq, delim);
        assert((i - 2) < intersperse_spec(sub_seq, delim).len());
        intersperse_spec_odd(sub_seq, delim, i - 2);
        assert(intersperse_spec(sub_seq, delim)[i - 2] == delim);
        assert(intersperse_spec(numbers, delim)[i] == intersperse_spec(sub_seq, delim)[i - 2]);
    }
}
// </vc-helpers>

// <vc-spec>
fn intersperse(numbers: &[i32], delim: i32) -> (res: Vec<i32>)
    // post-conditions-start
    ensures
        numbers.len() == 0 ==> res.len() == 0,
        numbers.len() != 0 ==> res.len() == 2 * numbers.len() - 1,
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 0 ==> res[i] == numbers[i / 2],
        forall|i: int| 0 <= i && i < res.len() && i % 2 == 1 ==> res[i] == delim
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if numbers.len() == 0 {
        return vec![];
    }
    
    let mut res = Vec::new();
    
    for i in 0..numbers.len()
        invariant
            res.len() == if i == 0 { 0 } else { 2 * i - 1 },
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 0 ==> res[j] == numbers[j / 2],
            forall|j: int| 0 <= j && j < res.len() && j % 2 == 1 ==> res[j] == delim
    {
        if i > 0 {
            res.push(delim);
        }
        res.push(numbers[i]);
    }
    
    res
}
// </vc-code>

fn main() {}
}