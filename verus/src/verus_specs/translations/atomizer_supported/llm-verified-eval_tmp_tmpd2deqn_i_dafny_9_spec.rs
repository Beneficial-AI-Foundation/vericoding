// ATOM 
pub open spec fn isMax(m: int, numbers: Seq<int>) -> bool
{
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

// SPEC 
pub fn max(numbers: Seq<int>) -> (result: int)
    requires
        numbers.len() != 0,
    ensures
        isMax(result, numbers),
{
}

// SPEC 
pub fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires
        numbers.len() != 0,
    ensures
        result.len() == numbers.len(),
        forall|i: int| 0 < i < result.len() ==> isMax(result[i], numbers.subrange(0, i+1)),
{
}