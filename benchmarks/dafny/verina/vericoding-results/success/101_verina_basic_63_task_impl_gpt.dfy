// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
function ExistsClose(numbers: array<int>, threshold: int): bool
    reads numbers
{
    exists i: int, j: int ::
        0 <= i < numbers.Length &&
        0 <= j < numbers.Length &&
        i != j &&
        AbsDiff(numbers[i], numbers[j]) < threshold
}
// </vc-helpers>

// <vc-spec>
method HasCloseElements(numbers: array<int>, threshold: int) returns (result: bool)
    requires threshold >= 0
    ensures
        !result <==> (forall i: int, j: int :: 
            0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j ==> 
            AbsDiff(numbers[i], numbers[j]) >= threshold)
// </vc-spec>
// <vc-code>
{
  result := ExistsClose(numbers, threshold);
}
// </vc-code>
