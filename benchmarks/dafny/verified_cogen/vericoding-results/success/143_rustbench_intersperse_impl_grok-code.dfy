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
/* code modified by LLM (iteration 2): implemented with loop and invariants to prove the intersperse postconditions */
{
  var n := numbers.Length;
  res := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == if i == 0 then 0 else (2 * i - 1)
    invariant forall j :: 0 <= j < |res| && j % 2 == 0 ==> res[j] == numbers[j / 2]
    invariant forall j :: 0 <= j < |res| && j % 2 == 1 ==> res[j] == delim
    decreases n - i
  {
    if i > 0 {
      res := res + [delim];
    }
    res := res + [numbers[i]];
    i := i + 1;
  }
}
// </vc-code>
