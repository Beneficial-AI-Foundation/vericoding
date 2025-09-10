predicate ValidInput(input: string)
{
    |input| >= 0
}

function SplitLines_func(input: string): seq<string>
    requires |input| >= 0
{
    if |input| == 0 then []
    else SplitLines_helper(input, 0, "", [])
}

function SplitLines_helper(input: string, i: int, current: string, acc: seq<string>): seq<string>
    requires 0 <= i <= |input|
    requires forall j :: 0 <= j < |current| ==> current[j] != '\n'
    decreases |input| - i
{
    if i == |input| then
        if |current| > 0 then acc + [current] else acc
    else if input[i] == '\n' then
        SplitLines_helper(input, i + 1, "", acc + [current])
    else
        SplitLines_helper(input, i + 1, current + [input[i]], acc)
}

function ParseInt_func(s: string): int
    requires |s| >= 0
    ensures ParseInt_func(s) >= 0
{
    if |s| == 0 then 0
    else ParseInt_helper(s, 0, 0)
}

function ParseInt_helper(s: string, i: int, acc: int): int
    requires 0 <= i <= |s|
    requires acc >= 0
    ensures ParseInt_helper(s, i, acc) >= 0
    decreases |s| - i
{
    if i == |s| || !('0' <= s[i] <= '9') then acc
    else ParseInt_helper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function BuildOutput_func(lines: seq<string>, n: int): string
    requires |lines| > 0
    requires n >= 0
    requires n <= |lines| - 1
{
    if n == 0 then ""
    else if n == 1 then ClassifySentence_func(lines[1])
    else BuildOutput_func(lines, n-1) + "\n" + ClassifySentence_func(lines[n])
}

function ClassifySentence_func(sentence: string): string
{
    if EndsWith_func(sentence, "lala.") && !StartsWith_func(sentence, "miao.") then "Freda's"
    else if StartsWith_func(sentence, "miao.") && !EndsWith_func(sentence, "lala.") then "Rainbow's" 
    else "OMG>.< I don't know!"
}

function StartsWith_func(s: string, prefix: string): bool
    requires |prefix| >= 0
{
    |prefix| <= |s| && (forall i :: 0 <= i < |prefix| ==> s[i] == prefix[i])
}

function EndsWith_func(s: string, suffix: string): bool
    requires |suffix| >= 0
{
    |suffix| <= |s| && (forall i :: 0 <= i < |suffix| ==> s[|s| - |suffix| + i] == suffix[i])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| >= 0
    ensures var lines := SplitLines_func(input); 
            if |lines| == 0 then result == ""
            else (var n := ParseInt_func(lines[0]);
                  result == BuildOutput_func(lines, min(n, |lines| - 1)))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines_func(input);
    if |lines| == 0 {
        return "";
    }
    
    var n := ParseInt_func(lines[0]);
    var m := min(n, |lines| - 1);
    result := BuildOutput_func(lines, m);
}
// </vc-code>

