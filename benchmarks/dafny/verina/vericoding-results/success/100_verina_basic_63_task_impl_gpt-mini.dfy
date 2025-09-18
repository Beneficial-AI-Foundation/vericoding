// <vc-preamble>
function AbsDiff(a: int, b: int): int
{
    if a >= b then a - b else b - a
}
// </vc-preamble>

// <vc-helpers>
function AbsDiffSymm(a: int, b: int): bool { AbsDiff(a,b) == AbsDiff(b,a) }
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
  result := exists i:int, j:int :: 0 <= i < numbers.Length && 0 <= j < numbers.Length && i != j && AbsDiff(numbers[i], numbers[j]) < threshold;
}
// </vc-code>
