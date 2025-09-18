// <vc-preamble>
datatype Option<T> = None | Some(value: T)

function CountChar(chars: seq<char>, c: char): nat
    decreases |chars|
{
    if |chars| == 0 then
        0
    else if chars[0] == c then
        1 + CountChar(chars[1..], c)
    else
        CountChar(chars[1..], c)
}

predicate HasNoDuplicatesUpTo(chars: seq<char>, endIdx: int)
    requires 0 <= endIdx <= |chars|
{
    forall i, j :: 0 <= i < j < endIdx ==> chars[i] != chars[j]
}

predicate HasNoDuplicates(chars: seq<char>)
{
    forall i, j :: 0 <= i < j < |chars| ==> chars[i] != chars[j]
}

function FirstOccurrenceIndex(chars: seq<char>, c: char): int
    requires exists i :: 0 <= i < |chars| && chars[i] == c
    ensures 0 <= FirstOccurrenceIndex(chars, c) < |chars|
    ensures chars[FirstOccurrenceIndex(chars, c)] == c
{
    if chars[0] == c then 0
    else 1 + FirstOccurrenceIndex(chars[1..], c)
}

predicate SecondOccurrenceExists(chars: seq<char>, c: char)
{
    exists i, j :: 0 <= i < j < |chars| && chars[i] == c && chars[j] == c
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed content as no helpers are necessary */
// </vc-helpers>

// <vc-spec>
method FindFirstRepeatedChar(s: array<char>) returns (result: Option<char>)
    ensures match result {
        case Some(c) => 
            var chars := s[..];
            CountChar(chars, c) >= 2 &&
            SecondOccurrenceExists(chars, c) &&
            (exists firstIdx :: 0 <= firstIdx < |chars| && chars[firstIdx] == c &&
             exists secondIdx :: firstIdx < secondIdx < |chars| && chars[secondIdx] == c &&
             HasNoDuplicatesUpTo(chars, secondIdx))
        case None => 
            HasNoDuplicates(s[..])
    }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): removed invalid `decreases *` for for loops */
{
    var chars := s[..];

    for i := 0 to |chars| - 1
    {
        var currentChar := chars[i];
        for j := i + 1 to |chars| - 1
        {
            if chars[j] == currentChar {
                if (HasNoDuplicatesUpTo(chars, j)) // This ensures 'j' is the first repeating occurrence index
                {
                    result := Some(currentChar);
                    return;
                }
            }
        }
    }

    result := None;
}
// </vc-code>
