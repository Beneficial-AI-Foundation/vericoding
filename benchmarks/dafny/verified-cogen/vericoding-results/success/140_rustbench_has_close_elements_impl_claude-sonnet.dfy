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
  flag := false;
  var i := 0;
  while i < numbers.Length && !flag
    invariant 0 <= i <= numbers.Length
    invariant flag == (exists k, l :: 0 <= k < i && 0 <= l < numbers.Length && k != l && AbsSpec(numbers[k] - numbers[l]) < threshold)
  {
    var j := 0;
    while j < numbers.Length && !flag
      invariant 0 <= j <= numbers.Length
      invariant flag == (exists k, l :: (0 <= k < i && 0 <= l < numbers.Length && k != l && AbsSpec(numbers[k] - numbers[l]) < threshold) || (k == i && 0 <= l < j && k != l && AbsSpec(numbers[k] - numbers[l]) < threshold))
    {
      if i != j {
        var diff := numbers[i] - numbers[j];
        var absDiff := if diff < 0 then -diff else diff;
        if absDiff < threshold {
          flag := true;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
