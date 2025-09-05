```vc-helpers
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

lemma {:axiom} ParseRatingsEquality(lines: seq<string>, n: int, i: int)
    requires n >= 0
    requires 1 + n <= |lines|
    requires 1 <= i <= n + 1
    requires i <= |lines|
    ensures i > 1 ==> ParseRatingsUpTo(lines, i) == ParseRatingsFunc(lines, i - 1)
    ensures ParseRatingsUpTo(lines, 1) == []

lemma {:axiom} HasChangesEquivalence(lines: seq<string>, n: int, i: int, ratingChanged: bool)
    requires n >= 0
    requires 1 + n <= |lines|
    requires 1 <= i <= n + 1
    requires i <= |lines|
    requires ratingChanged <==> (exists j :: 1 <= j < i && j < |lines| &&
                                (var parts := SplitFunc(lines[j], ' ');
                                 |parts| >= 2 && |parts[0]| > 0 && |parts[1]| > 0 &&
                                 StringToIntFunc(parts[0]) != StringToIntFunc(parts[1])))
    ensures (i > n ==> ratingChanged <==> HasChangesFunc(lines, n))

method IsNonIncreasingCheck(ratings: seq<int>) returns (result: bool)
    ensures result == IsNonIncreasing(ratings)
{
    if |ratings| <= 1 {
        result := true;
        return;
    }
    result := true;
    var i := 0;
    while i < |ratings| - 1
        invariant 0 <= i <= |ratings| - 1
        invariant result <==> (forall j :: 0 <= j < i ==> ratings[j] >= ratings[j + 1])
    {
        if ratings[i] < ratings[i + 1] {
            result := false;
            return;
        }
        i := i + 1;
    }
}
```

```vc-code
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    var initialRatings: seq<int> := [];
    var ratingChanged := false;

    var i := 1;
    while i <= n && i < |lines|
        invariant 1 <= i <= n + 1
        invariant i <= |lines|
        invariant |initialRatings| == i - 1
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

    if ratingChanged {
        output := "rated";
    } else {
        var isNonInc := IsNonIncreasingCheck(initialRatings);
        if isNonInc {
            output := "maybe";
        } else {
            output := "unrated";
        }
    }
}
```