// <vc-preamble>
function AbsSpec(i: int): int
{
    if i < 0 then -i else i
}
// </vc-preamble>

// <vc-helpers>
function absdiff(a: int, b: int): int { if a < b then b - a else a - b }
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
    var i := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant !(exists k, l :: 0 <= k < i && 0 <= l < numbers.Length && k != l && absdiff(numbers[k], numbers[l]) < threshold)
    {
        var j := 0;
        while j < numbers.Length
            invariant 0 <= j <= numbers.Length
            invariant i != j ==> !(exists k :: 0 <= k < j && k != i && absdiff(numbers[i], numbers[k]) < threshold)
        {
            if i != j && absdiff(numbers[i], numbers[j]) < threshold {
                flag := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    flag := false;
}
// </vc-code>
