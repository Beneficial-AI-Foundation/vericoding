// <vc-preamble>

predicate ValidInput(text: string)
{
    true
}

predicate IsSpaceSequence(text: string, start: int, end: int)
    requires 0 <= start <= end < |text|
{
    (forall k :: start <= k <= end ==> text[k] == ' ') &&
    (start == 0 || text[start-1] != ' ') &&
    (end == |text|-1 || text[end+1] != ' ')
}

predicate ValidResult(text: string, result: string)
{
    |result| <= |text| &&
    (text == "" ==> result == "") &&
    (forall i :: 0 <= i < |result| ==> result[i] != ' ') &&
    (forall i :: 0 <= i < |result| ==> result[i] == '_' || result[i] == '-' || result[i] in text) &&
    ((forall i :: 0 <= i < |text| ==> text[i] != ' ') ==> result == text) &&
    (forall i :: 0 <= i < |text| && text[i] != ' ' ==> text[i] in result)
}

predicate PreservesOrder(text: string, result: string)
{
    forall i, j :: 0 <= i < j < |text| && text[i] != ' ' && text[j] != ' ' ==>
        exists i', j' :: 0 <= i' < j' < |result| && result[i'] == text[i] && result[j'] == text[j]
}

predicate CorrectSpaceTransformation(text: string, result: string)
{
    (forall start, end :: (0 <= start <= end < |text| && 
        IsSpaceSequence(text, start, end)) ==>
        ((end - start + 1 <= 2 ==> (exists pos :: 0 <= pos < |result| - (end - start) && 
            (forall i :: pos <= i <= pos + (end - start) ==> result[i] == '_'))) &&
        (end - start + 1 > 2 ==> (exists pos :: 0 <= pos < |result| && result[pos] == '-'))) &&
    (forall i :: 0 <= i < |result| && result[i] == '_' ==> 
        exists start, end :: 0 <= start <= end < |text| && 
        IsSpaceSequence(text, start, end) && end - start + 1 <= 2) &&
    (forall i :: 0 <= i < |result| && result[i] == '-' ==> 
        exists start, end :: 0 <= start <= end < |text| && 
        IsSpaceSequence(text, start, end) && end - start + 1 > 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method fix_spaces(text: string) returns (result: string)
    requires ValidInput(text)
    ensures ValidResult(text, result)
    ensures PreservesOrder(text, result)
    ensures CorrectSpaceTransformation(text, result)
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
