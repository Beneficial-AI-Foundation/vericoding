// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 &&
    |SplitByNewlineFunc(input)| >= 2 && 
    |SplitBySpaceFunc(SplitByNewlineFunc(input)[0])| >= 2 && 
    |SplitBySpaceFunc(SplitByNewlineFunc(input)[1])| > 0
}

function GetHealth(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewlineFunc(input);
    var firstParts := SplitBySpaceFunc(lines[0]);
    ParseIntFunc(firstParts[0])
}

function GetTotalDamage(input: string): int
    requires ValidInput(input)
{
    var lines := SplitByNewlineFunc(input);
    var secondParts := SplitBySpaceFunc(lines[1]);
    SumAllDamageValues(secondParts)
}

function SumAllDamageValues(parts: seq<string>): int
{
    if |parts| == 0 then 0
    else ParseIntFunc(parts[0]) + SumAllDamageValues(parts[1..])
}

function SumFirstNDamageValues(parts: seq<string>, n: int): int
    requires n >= 0
{
    if |parts| == 0 || n == 0 then 0
    else if n > |parts| then SumAllDamageValues(parts)
    else ParseIntFunc(parts[0]) + SumFirstNDamageValues(parts[1..], n-1)
}

function SplitByNewlineFunc(s: string): seq<string>
    requires |s| >= 0
    ensures forall i :: 0 <= i < |SplitByNewlineFunc(s)| ==> '\n' !in SplitByNewlineFunc(s)[i]
{
    if |s| == 0 then []
    else 
        var newlinePos := FindChar(s, '\n', 0);
        if newlinePos == -1 then 
            assert '\n' !in s;
            [s]
        else if newlinePos == 0 then SplitByNewlineFunc(s[1..])
        else 
            assert '\n' !in s[0..newlinePos] by {
                forall k | 0 <= k < newlinePos ensures s[k] != '\n' {
                    assert s[k] != '\n' by { 
                        if s[k] == '\n' { 
                            assert FindChar(s, '\n', 0) <= k by { FindCharCorrect(s, '\n', 0, k); }
                            assert false;
                        }
                    }
                }
            }
            [s[0..newlinePos]] + SplitByNewlineFunc(s[newlinePos+1..])
}

function SplitBySpaceFunc(s: string): seq<string>
    requires |s| >= 0
    ensures forall i :: 0 <= i < |SplitBySpaceFunc(s)| ==> ' ' !in SplitBySpaceFunc(s)[i]
{
    if |s| == 0 then []
    else 
        var spacePos := FindChar(s, ' ', 0);
        if spacePos == -1 then 
            assert ' ' !in s;
            [s]
        else if spacePos == 0 then SplitBySpaceFunc(s[1..])
        else 
            assert ' ' !in s[0..spacePos] by {
                forall k | 0 <= k < spacePos ensures s[k] != ' ' {
                    assert s[k] != ' ' by { 
                        if s[k] == ' ' { 
                            assert FindChar(s, ' ', 0) <= k by { FindCharCorrect(s, ' ', 0, k); }
                            assert false;
                        }
                    }
                }
            }
            [s[0..spacePos]] + SplitBySpaceFunc(s[spacePos+1..])
}

function FindChar(s: string, c: char, start: int): int
    requires 0 <= start <= |s|
    ensures FindChar(s, c, start) == -1 || (start <= FindChar(s, c, start) < |s| && s[FindChar(s, c, start)] == c)
    ensures FindChar(s, c, start) == -1 ==> forall k :: start <= k < |s| ==> s[k] != c
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == c then start
    else FindChar(s, c, start + 1)
}

function ParseIntFunc(s: string): int
    requires |s| >= 0
    ensures ParseIntFunc(s) >= 0
    ensures |s| == 0 ==> ParseIntFunc(s) == 0
{
    if |s| == 0 then 0
    else ParseIntHelper(s, 0, 0)
}

function ParseIntHelper(s: string, pos: int, acc: int): int
    requires 0 <= pos <= |s|
    requires acc >= 0
    ensures ParseIntHelper(s, pos, acc) >= acc
    decreases |s| - pos
{
    if pos >= |s| || !(s[pos] >= '0' && s[pos] <= '9') then acc
    else ParseIntHelper(s, pos + 1, acc * 10 + (s[pos] as int - '0' as int))
}
// </vc-preamble>

// <vc-helpers>
lemma {:axiom} FindCharCorrect(s: string, c: char, start: int, pos: int)
    requires 0 <= start <= pos < |s|
    requires s[pos] == c
    ensures FindChar(s, c, start) <= pos

lemma SumFirstNIncremental(parts: seq<string>, i: int)
    requires 0 <= i < |parts|
    ensures SumFirstNDamageValues(parts, i+1) == SumFirstNDamageValues(parts, i) + ParseIntFunc(parts[i])
{
    if i == 0 {
        assert SumFirstNDamageValues(parts, 1) == ParseIntFunc(parts[0]);
        assert SumFirstNDamageValues(parts, 0) == 0;
    } else {
        SumFirstNIncremental(parts[1..], i-1);
    }
}

lemma SumFirstNEqualsAll(parts: seq<string>, n: int)
    requires n >= |parts|
    ensures SumFirstNDamageValues(parts, n) == SumAllDamageValues(parts)
{
    if |parts| == 0 {
        // Base case: empty sequence
    } else {
        // Recursive case
        SumFirstNEqualsAll(parts[1..], n-1);
    }
}

method SplitByNewline(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> '\n' !in parts[i]
    ensures parts == SplitByNewlineFunc(s)
{
    if |s| == 0 {
        parts := [];
        return;
    }

    var newlinePos := FindChar(s, '\n', 0);
    if newlinePos == -1 {
        parts := [s];
    } else if newlinePos == 0 {
        parts := SplitByNewline(s[1..]);
    } else {
        var rest := SplitByNewline(s[newlinePos+1..]);
        parts := [s[0..newlinePos]] + rest;

        assert forall k | 0 <= k < newlinePos :: s[k] != '\n' by {
            forall k | 0 <= k < newlinePos ensures s[k] != '\n' {
                if s[k] == '\n' {
                    FindCharCorrect(s, '\n', 0, k);
                    assert false;
                }
            }
        }

        assert forall i :: 0 <= i < |parts| ==> '\n' !in parts[i] by {
            forall i | 0 <= i < |parts| ensures '\n' !in parts[i] {
                if i == 0 {
                    assert parts[i] == s[0..newlinePos];
                } else {
                    assert parts[i] == rest[i-1];
                    assert '\n' !in rest[i-1];
                }
            }
        }
    }
}

method SplitBySpace(s: string) returns (parts: seq<string>)
    requires |s| >= 0
    ensures |parts| >= 0
    ensures forall i :: 0 <= i < |parts| ==> ' ' !in parts[i]
    ensures parts == SplitBySpaceFunc(s)
{
    if |s| == 0 {
        parts := [];
        return;
    }

    var spacePos := FindChar(s, ' ', 0);
    if spacePos == -1 {
        parts := [s];
    } else if spacePos == 0 {
        parts := SplitBySpace(s[1..]);
    } else {
        var rest := SplitBySpace(s[spacePos+1..]);
        parts := [s[0..spacePos]] + rest;

        assert forall k | 0 <= k < spacePos :: s[k] != ' ' by {
            forall k | 0 <= k < spacePos ensures s[k] != ' ' {
                if s[k] == ' ' {
                    FindCharCorrect(s, ' ', 0, k);
                    assert false;
                }
            }
        }

        assert forall i :: 0 <= i < |parts| ==> ' ' !in parts[i] by {
            forall i | 0 <= i < |parts| ensures ' ' !in parts[i] {
                if i == 0 {
                    assert parts[i] == s[0..spacePos];
                } else {
                    assert parts[i] == rest[i-1];
                    assert ' ' !in rest[i-1];
                }
            }
        }
    }
}

method ParseInt(s: string) returns (result: int)
    requires |s| >= 0
    ensures result >= 0
    ensures |s| == 0 ==> result == 0
    ensures result == ParseIntFunc(s)
{
    if |s| == 0 {
        result := 0;
        return;
    }

    result := ParseIntHelper(s, 0, 0);
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures result == "Yes\n" || result == "No\n"
    ensures ValidInput(input) ==>
        (var h := GetHealth(input);
         var totalDamage := GetTotalDamage(input);
         result == (if h <= totalDamage then "Yes\n" else "No\n"))
    ensures !ValidInput(input) ==> result == "No\n"
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    assert lines == SplitByNewlineFunc(input);
    if |lines| < 2 {
        result := "No\n";
        return;
    }

    var firstLineParts := SplitBySpace(lines[0]);
    assert firstLineParts == SplitBySpaceFunc(lines[0]);
    if |firstLineParts| < 2 {
        result := "No\n";
        return;
    }

    var secondLineParts := SplitBySpace(lines[1]);
    assert secondLineParts == SplitBySpaceFunc(lines[1]);
    if |secondLineParts| == 0 {
        result := "No\n";
        return;
    }

    var h := ParseInt(firstLineParts[0]);
    assert h == ParseIntFunc(firstLineParts[0]);
    var n := ParseInt(firstLineParts[1]);

    var totalDamage := 0;

    var i := 0;
    while i < |secondLineParts|
        invariant 0 <= i <= |secondLineParts|
        invariant totalDamage == SumFirstNDamageValues(secondLineParts, i)
    {
        var damage := ParseInt(secondLineParts[i]);
        assert damage == ParseIntFunc(secondLineParts[i]);
        totalDamage := totalDamage + damage;

        SumFirstNIncremental(secondLineParts, i);

        i := i + 1;
    }

    assert i == |secondLineParts|;
    assert totalDamage == SumFirstNDamageValues(secondLineParts, |secondLineParts|);
    SumFirstNEqualsAll(secondLineParts, |secondLineParts|);
    assert totalDamage == SumAllDamageValues(secondLineParts);

    if h <= totalDamage {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
// </vc-code>
