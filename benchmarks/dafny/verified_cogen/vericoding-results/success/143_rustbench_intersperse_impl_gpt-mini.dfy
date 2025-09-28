// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added min helper */
function min(a: int, b: int): int { if a < b then a else b }
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
  /* code modified by LLM (iteration 2): build interspersed sequence iteratively */
  if numbers.Length == 0 {
    res := [];
    return;
  }
  var s := [numbers[0]];
  var i := 1;
  while i < numbers.Length
    invariant 1 <= i <= numbers.Length
    invariant |s| == 2 * i - 1
    invariant forall j :: 0 <= j < |s| && j % 2 == 0 ==> s[j] == numbers[j / 2]
    invariant forall j :: 0 <= j < |s| && j % 2 == 1 ==> s[j] == delim
  {
    s := s + [delim, numbers[i]];
    i := i + 1;
  }
  res := s;
}
// </vc-code>
