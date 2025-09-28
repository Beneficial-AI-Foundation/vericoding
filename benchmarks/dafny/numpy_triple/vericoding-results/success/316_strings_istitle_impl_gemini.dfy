// <vc-preamble>
// Helper predicates for character classification
predicate IsUpper(c: char)
{
    'A' <= c <= 'Z'
}

predicate IsLower(c: char)
{
    'a' <= c <= 'z'
}

predicate IsAlpha(c: char)
{
    IsUpper(c) || IsLower(c)
}

predicate IsCased(c: char)
{
    IsUpper(c) || IsLower(c)
}

// Helper predicate to check if sequence contains at least one cased character
predicate HasCasedChar(chars: seq<char>)
{
    exists i :: 0 <= i < |chars| && IsCased(chars[i])
}

// Recursive helper to check titlecase pattern
predicate CheckTitleCase(chars: seq<char>, expectUpper: bool)
    decreases |chars|
{
    if |chars| == 0 then
        true
    else
        var c := chars[0];
        var rest := chars[1..];
        if IsUpper(c) then
            expectUpper && CheckTitleCase(rest, false)
        else if IsLower(c) then
            !expectUpper && CheckTitleCase(rest, false)
        else
            // Non-alphabetic character - next alphabetic char should be uppercase
            CheckTitleCase(rest, true)
}

// Main predicate to determine if a string is titlecased
predicate IsTitlecased(s: string)
{
    |s| > 0 &&
    HasCasedChar(s) &&
    CheckTitleCase(s, true)
}

// Main method implementing numpy.strings.istitle
// </vc-preamble>

// <vc-helpers>
method ComputeHasCasedChar(chars: seq<char>) returns (result: bool)
    ensures result == HasCasedChar(chars)
{
    result := false;
    var i := 0;
    while i < |chars|
        invariant 0 <= i <= |chars|
        invariant result <==> (exists j :: 0 <= j < i && IsCased(chars[j]))
    {
        if IsCased(chars[i]) {
            result := true;
            return;
        }
        i := i + 1;
    }
}

method ComputeCheckTitleCase(chars: seq<char>, expectUpper: bool) returns (result: bool)
    decreases |chars|
    ensures result == CheckTitleCase(chars, expectUpper)
{
    if |chars| == 0 {
        result := true;
    } else {
        var c := chars[0];
        var rest := chars[1..];
        if IsUpper(c) {
            if expectUpper {
                result := ComputeCheckTitleCase(rest, false);
            } else {
                result := false;
            }
        } else if IsLower(c) {
            if !expectUpper {
                result := ComputeCheckTitleCase(rest, false);
            } else {
                result := false;
            }
        } else {
            result := ComputeCheckTitleCase(rest, true);
        }
    }
}

method ComputeIsTitlecased(s: string) returns (result: bool)
    ensures result == IsTitlecased(s)
{
    if |s| == 0 {
        result := false;
        return;
    }
    var hasCased := ComputeHasCasedChar(s);
    if !hasCased {
        result := false;
        return;
    }
    result := ComputeCheckTitleCase(s, true);
}
// </vc-helpers>

// <vc-spec>
method istitle(a: seq<string>) returns (result: seq<bool>)
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |a| ==> result[i] == IsTitlecased(a[i])
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == IsTitlecased(a[j])
    {
        var is_title_val := ComputeIsTitlecased(a[i]);
        result := result + [is_title_val];
        i := i + 1;
    }
}
// </vc-code>
