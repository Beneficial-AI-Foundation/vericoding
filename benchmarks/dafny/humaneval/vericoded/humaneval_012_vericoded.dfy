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

// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures ValidResult(strings, result)
// </vc-spec>
// <vc-code>
{
  if |strings| == 0 {
    result := None;
  } else {
    var maxLen := |strings[0]|;
    var maxIdx := 0;
    var i := 1;
    while i < |strings|
      invariant 0 <= i <= |strings|
      invariant 0 <= maxIdx < |strings|
      invariant maxLen == |strings[maxIdx]|
      invariant forall j :: 0 <= j < i ==> |strings[j]| <= maxLen
      invariant forall j :: 0 <= j < maxIdx ==> |strings[j]| < maxLen
    {
      if |strings[i]| > maxLen {
        maxLen := |strings[i]|;
        maxIdx := i;
      }
      i := i + 1;
    }
    result := Some(strings[maxIdx]);
  }
}
// </vc-code>
