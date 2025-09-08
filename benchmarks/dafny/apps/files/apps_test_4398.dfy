Given two strings S and T of equal length N, create a new string by alternating characters 
from S and T in the order: S[0], T[0], S[1], T[1], ..., S[N-1], T[N-1].

predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 2 &&
    (var n := StringToInt(lines[0]);
     var parts := SplitBySpace(lines[1]);
     |parts| >= 2 &&
     n >= 0 &&
     n <= |parts[0]| && n <= |parts[1]|)
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    StringToInt(lines[0])
}

function GetS(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[0]
}

function GetT(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[1]
}

function AlternateChars(s: string, t: string, n: int): string
    requires n >= 0
    requires n <= |s| && n <= |t|
    ensures |AlternateChars(s, t, n)| == 2 * n
    ensures forall i :: 0 <= i < n ==> 
        i * 2 < |AlternateChars(s, t, n)| && 
        i * 2 + 1 < |AlternateChars(s, t, n)| &&
        AlternateChars(s, t, n)[i * 2] == s[i] && 
        AlternateChars(s, t, n)[i * 2 + 1] == t[i]
{
    if n == 0 then ""
    else [s[0]] + [t[0]] + AlternateChars(s[1..], t[1..], n - 1)
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, '\n');
        if pos == -1 then [s]
        else if pos < |s| then [s[0..pos]] + SplitLines(s[pos+1..])
        else [s]
}

function SplitBySpace(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var pos := FindChar(s, ' ');
        if pos == -1 then [s]
        else if pos < |s| then [s[0..pos]] + SplitBySpace(s[pos+1..])
        else [s]
}

function FindChar(s: string, c: char): int
    ensures -1 <= FindChar(s, c) < |s|
{
    FindCharHelper(s, c, 0)
}

function FindCharHelper(s: string, c: char, index: int): int
    requires 0 <= index
    ensures -1 <= FindCharHelper(s, c, index) < |s|
    decreases |s| - index
{
    if index >= |s| then -1
    else if s[index] == c then index
    else FindCharHelper(s, c, index + 1)
}

function StringToInt(s: string): int
    ensures StringToInt(s) >= 0
{
    if |s| == 0 then 0
    else StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, index: int, acc: int): int
    requires 0 <= index
    requires acc >= 0
    ensures StringToIntHelper(s, index, acc) >= 0
    decreases |s| - index
{
    if index >= |s| then acc
    else
        var digit := s[index] as int - '0' as int;
        if 0 <= digit <= 9 then
            StringToIntHelper(s, index + 1, acc * 10 + digit)
        else
            acc
}

lemma AlternateCharsIterativeEquivalence(s: string, t: string, n: int, ans: string)
    requires n >= 0
    requires n <= |s| && n <= |t|
    requires |ans| == 2 * n
    requires forall i :: 0 <= i < n ==> 
        i * 2 < |ans| && i * 2 + 1 < |ans| &&
        ans[i * 2] == s[i] && ans[i * 2 + 1] == t[i]
    ensures ans == AlternateChars(s, t, n)
{
    if n == 0 {
        assert ans == "";
        assert AlternateChars(s, t, n) == "";
    } else {
        var ans_rest := ans[2..];
        assert |ans_rest| == 2 * (n - 1);
        assert forall i :: 0 <= i < n - 1 ==> 
            i * 2 < |ans_rest| && i * 2 + 1 < |ans_rest| &&
            ans_rest[i * 2] == s[i + 1] && ans_rest[i * 2 + 1] == t[i + 1];
        AlternateCharsIterativeEquivalence(s[1..], t[1..], n - 1, ans_rest);
        assert ans_rest == AlternateChars(s[1..], t[1..], n - 1);
        assert ans == [s[0]] + [t[0]] + ans_rest;
        assert ans == [s[0]] + [t[0]] + AlternateChars(s[1..], t[1..], n - 1);
        assert ans == AlternateChars(s, t, n);
    }
}

method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==> 
        (var n := GetN(input);
         var s := GetS(input);
         var t := GetT(input);
         |result| == 2 * n + 1 &&
         result[|result| - 1] == '\n' &&
         result[0..|result|-1] == AlternateChars(s, t, n))
    ensures !ValidInput(input) ==> result == ""
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        result := "";
        return;
    }

    var n := StringToInt(lines[0]);
    var parts := SplitBySpace(lines[1]);
    if |parts| < 2 {
        result := "";
        return;
    }

    var s := parts[0];
    var t := parts[1];

    if n > |s| || n > |t| {
        result := "";
        return;
    }

    var ans := "";
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant n <= |s| && n <= |t|
        invariant |ans| == 2 * i
        invariant forall j :: 0 <= j < i ==> 
            j * 2 < |ans| && j * 2 + 1 < |ans| &&
            ans[j * 2] == s[j] && ans[j * 2 + 1] == t[j]
    {
        ans := ans + [s[i]] + [t[i]];
        i := i + 1;
    }

    AlternateCharsIterativeEquivalence(s, t, n, ans);
    result := ans + ['\n'];
}
