pub fn count_less_than(numbers: Set<int>, threshold: int) -> (count: int)
    ensures count == (numbers.filter(|i: int| *i < threshold)).len()
{
}