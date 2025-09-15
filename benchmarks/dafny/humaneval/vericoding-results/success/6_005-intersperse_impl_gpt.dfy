// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): retained predicate for odd indices */
predicate IsOddIndexDelim(res: seq<int>, delimiter: int) { forall i:int :: 0 <= i < |res| && i % 2 == 1 ==> res[i] == delimiter }
/* helper modified by LLM (iteration 2): added range guard to avoid out-of-bounds access on numbers */
predicate MatchesEvenIndices(res: seq<int>, numbers: seq<int>) { forall i:int :: 0 <= i < |res| && i % 2 == 0 ==> i / 2 < |numbers| && res[i] == numbers[i / 2] }
/* helper modified by LLM (iteration 2): length function for intersperse */
function IntersperseTargetLength(n: nat): nat { if n == 0 then 0 else 2*n - 1 }
// </vc-helpers>

// <vc-spec>
method intersperse(numbers: seq<int>, delimeter: int) returns (res: seq<int>)

  ensures |numbers| != 0 ==> |numbers| * 2 - 1 == |res|
  ensures |numbers| == 0 ==> |res| == 0
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 0 ==> res[i] == numbers[i / 2]
  ensures forall i : int :: i >= 0 && i < |res| && i % 2 == 1 ==> res[i] == delimeter
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): implemented intersperse construction with loop and invariants */
  res := [];
  if |numbers| == 0 {
    return;
  }
  res := [numbers[0]];
  var i := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant |res| == 2*i - 1
    invariant forall j:int :: 0 <= j < |res| && j % 2 == 1 ==> res[j] == delimeter
    invariant forall j:int :: 0 <= j < |res| && j % 2 == 0 ==> res[j] == numbers[j / 2]
    decreases |numbers| - i
  {
    res := res + [delimeter, numbers[i]];
    i := i + 1;
  }
}
// </vc-code>
