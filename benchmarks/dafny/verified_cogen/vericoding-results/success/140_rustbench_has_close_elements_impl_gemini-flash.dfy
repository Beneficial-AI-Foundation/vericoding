// <vc-preamble>
function AbsSpec(i: int): int
{
    if i < 0 then -i else i
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method HasCloseElements(numbers: array<int>, threshold: int) returns (flag: bool)
    requires threshold > 0
    requires forall i, j :: 0 <= i < numbers.Length && 0 <= j < numbers.Length ==> 
        numbers[i] - numbers[j] < 0x7FFFFFFF && -(numbers[i] - numbers[j]) < 0x7FFFFFFF
    ensures flag == (exists i, j :: 
        0 <= i < numbers.Length && 0 <= j < numbers.Length && 
        i != j && AbsSpec(numbers[i] - numbers[j]) < threshold)
// </vc-spec>
// <vc-code>
{
    var i: int := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant forall x, y :: 0 <= x < i && 0 <= y < numbers.Length && x != y ==> AbsSpec(numbers[x] - numbers[y]) >= threshold
    {
        var j: int := 0;
        while j < numbers.Length
            invariant 0 <= j <= numbers.Length
            invariant forall y :: 0 <= y < j && i != y ==> AbsSpec(numbers[i] - numbers[y]) >= threshold
            invariant forall x, y :: 0 <= x < i && 0 <= y < numbers.Length && x != y ==> AbsSpec(numbers[x] - numbers[y]) >= threshold
        {
            if i != j {
                if AbsSpec(numbers[i] - numbers[j]) < threshold {
                    return true;
                }
            }
            j := j + 1;
        }
        i := i + 1;
    }
    return false;
}
// </vc-code>
