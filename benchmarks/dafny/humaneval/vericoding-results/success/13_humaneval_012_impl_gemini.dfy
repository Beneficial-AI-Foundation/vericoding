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
    var longest_idx := 0;
    var i := 1;
    while i < |strings|
      invariant 1 <= i <= |strings|
      invariant 0 <= longest_idx < i
      invariant forall j :: 0 <= j < i ==> |strings[longest_idx]| >= |strings[j]|
      invariant forall j :: 0 <= j < longest_idx ==> |strings[j]| < |strings[longest_idx]|
    {
      if |strings[i]| > |strings[longest_idx]| {
        longest_idx := i;
      }
      i := i + 1;
    }
    result := Some(strings[longest_idx]);
  }
}
// </vc-code>
