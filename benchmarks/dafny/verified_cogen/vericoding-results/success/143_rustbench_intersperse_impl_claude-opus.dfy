// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Intersperse(numbers: array<int>, delim: int) returns (res: seq<int>)
    ensures
        numbers.Length == 0 ==> |res| == 0
    ensures
        numbers.Length != 0 ==> |res| == 2 * numbers.Length - 1
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
    ensures
        forall i :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delim
// </vc-spec>
// <vc-code>
{
  if numbers.Length == 0 {
    res := [];
  } else {
    res := [numbers[0]];
    var i := 1;
    while i < numbers.Length
      invariant 1 <= i <= numbers.Length
      invariant |res| == 2 * i - 1
      invariant forall j :: 0 <= j < |res| && j % 2 == 0 ==> res[j] == numbers[j / 2]
      invariant forall j :: 0 <= j < |res| && j % 2 == 1 ==> res[j] == delim
    {
      res := res + [delim, numbers[i]];
      i := i + 1;
    }
  }
}
// </vc-code>
