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
/* helper modified by LLM (iteration 2): changed lemma to executable method that returns index of first longest string */
method FirstMaxIndex(strings: seq<string>) returns (i: int)
  requires |strings| > 0
  ensures 0 <= i < |strings|
  ensures forall j :: 0 <= j < |strings| ==> |strings[i]| >= |strings[j]|
  ensures forall j :: 0 <= j < i ==> |strings[j]| < |strings[i]|
{
  var idx := 0;
  var k := 1;
  while k < |strings|
    invariant 0 <= idx < |strings|
    invariant 0 <= k <= |strings|
    invariant forall j :: 0 <= j < k ==> |strings[idx]| >= |strings[j]|
    invariant forall j :: 0 <= j < idx ==> |strings[j]| < |strings[idx]|
  {
    if |strings[k]| > |strings[idx]| {
      idx := k;
    }
    k := k + 1;
  }
  i := idx;
}
// </vc-helpers>

// <vc-spec>
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures ValidResult(strings, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use FirstMaxIndex method to compute the first longest string and return it */
  if |strings| == 0 {
    result := None;
    return;
  }
  var i := FirstMaxIndex(strings);
  result := Some(strings[i]);
}
// </vc-code>
