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
    var bestIndex := 0;
    var best := strings[0];
    var i := 1;
    while i < |strings|
      invariant 0 <= bestIndex < i
      invariant i <= |strings|
      invariant best == strings[bestIndex]
      invariant forall j :: 0 <= j < i ==> |strings[j]| <= |best|
      invariant forall j :: 0 <= j < bestIndex ==> |strings[j]| < |best|
      decreases |strings| - i
    {
      if |strings[i]| > |best| {
        bestIndex := i;
        best := strings[i];
      }
      i := i + 1;
    }
    result := Some(best);
  }
}
// </vc-code>
