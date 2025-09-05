This verification task determines if a competitive programming round is rated, unrated, or indeterminate based on participant standings and rating changes. If any participant's rating changed, the round is definitely rated. If the round was rated and a participant with lower initial rating placed better than a participant with higher initial rating, then at least one rating must have changed. The implementation should output "rated" if definitely rated, "unrated" if definitely unrated, or "maybe" if indeterminate.

// ======= TASK =======
// Determine if a competitive programming round is rated, unrated, or indeterminate based on
// participant standings and rating changes. If any participant's rating changed, the round
// is definitely rated. If the round was rated and a participant with lower initial rating
// placed better than a participant with higher initial rating, then at least one rating
// must have changed. Output "rated" if definitely rated, "unrated" if definitely unrated,
// or "maybe" if indeterminate.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 &&
    var lines := SplitFunc(input, '\n');
    |lines| > 0 && |lines[0]| > 0 &&
    var n := StringToIntFunc(lines[0]);
    n >= 1 && 1 + n <= |lines|
}

function SplitFunc(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else SplitHelper(s, delimiter, 0, "")
}

function SplitHelper(s: string, delimiter: char, index: int, current: string): seq<string>
    requires 0 <= index <= |s|
    decreases |s| - index
{
    if index == |s| then
        if |current| > 0 then [current] else []
    else if s[index] == delimiter then
        [current] + SplitHelper(s, delimiter, index + 1, "")
    else
        SplitHelper(s, delimiter, index + 1, current + [s[index]])
}

function StringToIntFunc(s: string): int
    requires |s| > 0
{
    if |s| > 0 && s[0] == '-' then
        -StringToIntHelper(s, 1)
    else
        StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, start: int): int
    requires 0 <= start <= |s|
    decreases |s| - start
{
    if start >= |s| then 0
    else if '0' <= s[start] <= '9' then
        StringToIntHelper(s, start + 1) + (s[start] as int - '0' as int) * Power10(|s| - start - 1)
    else
        StringToIntHelper(s, start + 1)
}

function Power10(n: int): int
    requires n >= 0
    decreases n
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function ParseRatingsFunc(lines: seq<string>, n: int): seq<int>
    requires n >= 0
    requires 1 + n <= |lines|
{
    ParseRatingsUpTo(lines, n + 1)
}

function ParseRatingsUpTo(lines: seq<string>, upperBound: int): seq<int>
    requires upperBound >= 1
    requires upperBound <= |lines|
{
    if upperBound == 1 then []
    else
        var parts := SplitFunc(lines[upperBound - 1], ' ');
        if |parts| >= 2 && |parts[0]| > 0 then
            ParseRatingsUpTo(lines, upperBound - 1) + [StringToIntFunc(parts[0])]
        else
            ParseRatingsUpTo(lines, upperBound - 1)
}

function HasChangesFunc(lines: seq<string>, n: int): bool
    requires n >= 0
    requires 1 + n <= |lines|
{
    exists i :: 1 <= i <= n && i < |lines| &&
                (var parts := SplitFunc(lines[i], ' ');
                 |parts| >= 2 && |parts[0]| > 0 && |parts[1]| > 0 && 
                 StringToIntFunc(parts[0]) != StringToIntFunc(parts[1]))
}

predicate IsNonIncreasing(ratings: seq<int>)
{
    forall i :: 0 <= i < |ratings| - 1 ==> ratings[i] >= ratings[i + 1]
}

// ======= HELPERS =======
method Split(s: string, delimiter: char) returns (parts: seq<string>)
    ensures parts == SplitFunc(s, delimiter)
{
    if |s| == 0 {
        parts := [""];
        return;
    }
    parts := SplitImplHelper(s, delimiter, 0, "");
}

method SplitImplHelper(s: string, delimiter: char, index: int, current: string) returns (result: seq<string>)
    requires 0 <= index <= |s|
    ensures result == SplitHelper(s, delimiter, index, current)
    decreases |s| - index
{
    if index == |s| {
        if |current| > 0 {
            result := [current];
        } else {
            result := [];
        }
    } else if s[index] == delimiter {
        var rest := SplitImplHelper(s, delimiter, index + 1, "");
        result := [current] + rest;
    } else {
        result := SplitImplHelper(s, delimiter, index + 1, current + [s[index]]);
    }
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    ensures result == StringToIntFunc(s)
{
    if |s| > 0 && s[0] == '-' {
        var posResult := StringToIntImplHelper(s, 1);
        result := -posResult;
    } else {
        result := StringToIntImplHelper(s, 0);
    }
}

method StringToIntImplHelper(s: string, start: int) returns (result: int)
    requires 0 <= start <= |s|
    ensures result == StringToIntHelper(s, start)
    decreases |s| - start
{
    if start >= |s| {
        result := 0;
    } else if '0' <= s[start] <= '9' {
        var rest := StringToIntImplHelper(s, start + 1);
        result := rest + (s[start] as int - '0' as int) * Power10(|s| - start - 1);
    } else {
        result := StringToIntImplHelper(s, start + 1);
    }
}

// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures output == "rated" || output == "maybe" || output == "unrated"
    ensures var lines := SplitFunc(input, '\n');
            var n := StringToIntFunc(lines[0]);
            var ratings := ParseRatingsFunc(lines, n);
            var changes := HasChangesFunc(lines, n);
            (changes ==> output == "rated") &&
            (!changes && IsNonIncreasing(ratings) ==> output == "maybe") &&
            (!changes && !IsNonIncreasing(ratings) ==> output == "unrated")
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    var initialRatings: seq<int> := [];
    var ratingChanged := false;

    var i := 1;
    while i <= n && i < |lines|
        invariant 1 <= i <= n + 1
        invariant i <= |lines|
        invariant |initialRatings| <= i - 1
        invariant ratingChanged <==> (exists j :: 1 <= j < i && j < |lines| &&
                                     (var parts := SplitFunc(lines[j], ' ');
                                      |parts| >= 2 && |parts[0]| > 0 && |parts[1]| > 0 &&
                                      StringToIntFunc(parts[0]) != StringToIntFunc(parts[1])))
        invariant initialRatings == ParseRatingsUpTo(lines, i)
    {
        var parts := Split(lines[i], ' ');
        if |parts| >= 2 && |parts[0]| > 0 {
            var before := StringToInt(parts[0]);
            initialRatings := initialRatings + [before];
            if |parts[1]| > 0 {
                var after := StringToInt(parts[1]);
                if before != after {
                    ratingChanged := true;
                }
            }
        }
        i := i + 1;
    }

    assert ratingChanged <==> HasChangesFunc(lines, n);
    assert initialRatings == ParseRatingsFunc(lines, n);

    if ratingChanged {
        return "rated";
    } else if IsNonIncreasing(initialRatings) {
        return "maybe";
    } else {
        return "unrated";
    }
}
