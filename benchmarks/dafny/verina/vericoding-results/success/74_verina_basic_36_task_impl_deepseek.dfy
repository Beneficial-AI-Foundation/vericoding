// <vc-preamble>
predicate IsSpaceCommaDot(c: char)
{
    c == ' ' || c == ',' || c == '.'
}
// </vc-preamble>

// <vc-helpers>

function BuildString(s: string, index: int): string
    requires 0 <= index <= |s|
    ensures |BuildString(s, index)| == |s| - index
    ensures forall j :: 0 <= j < |s| - index ==> BuildString(s, index)[j] == s[index + j]
decreases |s| - index
{
    if index == |s| then
        ""
    else
        [s[index]] + BuildString(s, index + 1)
}

function ProcessChar(c: char): char
    ensures ProcessChar(c) == (if IsSpaceCommaDot(c) then ':' else c)
{
    if IsSpaceCommaDot(c) then ':' else c
}

// </vc-helpers>

// <vc-spec>
method ReplaceWithColon(s: string) returns (result: string)
    ensures
        |result| == |s|
    ensures
        forall i :: 0 <= i < |s| ==> 
            result[i] == 
            if IsSpaceCommaDot(s[i]) then ':' else s[i]
// </vc-spec>
// <vc-code>
{
    result := "";
    var i := 0;
    while i < |s|
        invariant |result| == i
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> result[j] == (if IsSpaceCommaDot(s[j]) then ':' else s[j])
    {
        result := result + [ProcessChar(s[i])];
        i := i + 1;
    }
}
// </vc-code>
