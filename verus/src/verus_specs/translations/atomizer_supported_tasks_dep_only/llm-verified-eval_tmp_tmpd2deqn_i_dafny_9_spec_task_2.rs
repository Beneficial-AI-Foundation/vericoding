pub fn is_max(m: int, numbers: Seq<int>) -> bool {
    numbers.contains(m) &&
    forall|i: int| 0 <= i < numbers.len() ==> numbers[i] <= m
}

pub fn rolling_max(numbers: Seq<int>) -> (result: Seq<int>)
    requires(
        numbers.len() != 0
    )
    ensures(|result: Seq<int>| {
        &&& result.len() == numbers.len()
        &&& forall|i: int| 0 < i < result.len() ==> is_max(result[i], numbers.subrange(0, i + 1))
    })
{
}