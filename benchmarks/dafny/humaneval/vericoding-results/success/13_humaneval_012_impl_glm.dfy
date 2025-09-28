// <vc-preamble>

datatype Option<T> = Some(value: T) | None

predicate ValidResult(strings: seq<string>, result: Option<string>)
{
    if |strings| == 0 then
        result == None
    else
        result.Some? &&
        (exists i :: (0 <= i < |strings| && strings[i] == result.value &&
        (forall s :: s in strings ==> |result.value| >= |s|) &&
        (forall j :: 0 <= j < i ==> |strings[j]| < |result.value|)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added decreases clause for termination */
function findFirstMaxIndex(strings: seq<string>, maxLength: int, start: int): int
  requires 0 <= start < |strings|
  requires forall j :: 0 <= j < |strings| ==> |strings[j]| <= maxLength
  requires exists j :: start <= j < |strings| && |strings[j]| == maxLength
  ensures start <= findFirstMaxIndex(strings, maxLength, start) < |strings|
  ensures |strings[findFirstMaxIndex(strings, maxLength, start)]| == maxLength
  ensures forall j :: start <= j < findFirstMaxIndex(strings, maxLength, start) ==> |strings[j]| < maxLength
  decreases |strings| - start
{
  if start == |strings| - 1 || |strings[start]| == maxLength then start
  else findFirstMaxIndex(strings, maxLength, start + 1)
}
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures ValidResult(strings, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): added invariant for i bounds to help verifier */
{
  if |strings| == 0 {
    return None;
  } else {
    var maxIndex := 0;
    var maxLength := |strings[0]|;
    var i := 1;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant 0 <= maxIndex < |strings|
      invariant maxLength == |strings[maxIndex]|
      invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLength
      invariant forall j :: 0 <= j < maxIndex ==> |strings[j]| < maxLength
    {
      if |strings[i]| > maxLength {
        maxIndex := i;
        maxLength := |strings[i]|;
      }
      i := i + 1;
    }
    var firstMaxIndex := findFirstMaxIndex(strings, maxLength, 0);
    return Some(strings[firstMaxIndex]);
  }
}
// </vc-code>
