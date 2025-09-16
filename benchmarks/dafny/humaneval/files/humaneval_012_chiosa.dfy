// <vc-preamble>
// ======= TASK =======
// Given a list of strings, return the longest string. If multiple strings have the same maximum length, 
// return the first one that appears in the list. If the list is empty, return None.

// ======= SPEC REQUIREMENTS =======
datatype Option<T> = Some(value: T) | None

predicate ValidResult(strings: seq<string>, result: Option<string>)
{
    if |strings| == 0 then
        result == None
    else
        result.Some? &&
        exists i :: 0 <= i < |strings| && strings[i] == result.value &&
        (forall s :: s in strings ==> |result.value| >= |s|) &&
        (forall j :: 0 <= j < i ==> |strings[j]| < |result.value|)
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method longest(strings: seq<string>) returns (result: Option<string>)
    ensures ValidResult(strings, result)
// </vc-spec>
// <vc-code>
{
    if |strings| == 0 {
        result := None;
    } else {
        result := Some(strings[0]);
        var bestIndex := 0;
        for i := 1 to |strings|
            invariant result.Some?
            invariant 0 <= bestIndex < i
            invariant strings[bestIndex] == result.value
            invariant forall s :: s in strings[0..i] ==> |result.value| >= |s|
            invariant forall j :: 0 <= j < bestIndex ==> |strings[j]| < |result.value|
        {
            if |strings[i]| > |result.value| {
                result := Some(strings[i]);
                bestIndex := i;
            }
        }
    }
}
// </vc-code>
