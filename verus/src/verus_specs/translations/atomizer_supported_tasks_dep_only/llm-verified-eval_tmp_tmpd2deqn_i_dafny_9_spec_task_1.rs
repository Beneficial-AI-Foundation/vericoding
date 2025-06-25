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

//ATOM_PLACEHOLDER_rolling_max