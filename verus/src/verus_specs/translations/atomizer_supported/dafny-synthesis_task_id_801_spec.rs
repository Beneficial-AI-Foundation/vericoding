pub fn count_equal_numbers(a: int, b: int, c: int) -> (count: int)
    ensures(count >= 0 && count <= 3)
    ensures((count == 3) <==> (a == b && b == c))
    ensures((count == 2) <==> ((a == b && b != c) || (a != b && b == c) || (a == c && b != c)))
    ensures((count == 1) <==> (a != b && b != c && a != c))
{
}