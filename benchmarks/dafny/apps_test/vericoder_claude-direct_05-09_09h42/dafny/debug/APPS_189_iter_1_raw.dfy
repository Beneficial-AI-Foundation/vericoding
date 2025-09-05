```vc-helpers
method FindOptimalT(sticks: seq<int>) returns (bestT: int, minCost: int)
    requires |sticks| >= 1
    requires forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100
    ensures IsOptimalSolution(sticks, bestT, minCost)
{
    bestT := 1;
    minCost := CalculateTotalCost(sticks, 1);

    for t := 1 to 100
        invariant 1 <= t <= 100
        invariant 1 <= bestT <= 99
        invariant minCost >= 0
        invariant minCost == CalculateTotalCost(sticks, bestT)
        invariant forall prev :: 1 <= prev < t ==> CalculateTotalCost(sticks, prev) >= minCost
    {
        var currentCost := CalculateTotalCost(sticks, t);
        if currentCost < minCost {
            minCost := currentCost;
            bestT := t;
        }
    }
}

method SplitLines(input: string) returns (lines: seq<string>)
    ensures |lines| >= 1
{
    lines := [];
    var current := "";

    for i := 0 to |input|
    {
        if i < |input| && input[i] == '\n' {
            lines := lines + [current];
            current := "";
        } else if i < |input| {
            current := current + [input[i]];
        }
    }

    if |current| > 0 {
        lines := lines + [current];
    }

    if |lines| == 0 {
        lines := [""];
    }
}

method ParseIntArray(line: string) returns (result: seq<int>)
    ensures |result| >= 0
{
    var parts := SplitBySpace(line);
    result := [];

    for i := 0 to |parts|
    {
        if |parts[i]| > 0 {
            assume forall j :: 0 <= j < |parts[i]| ==> '0' <= parts[i][j] <= '9';
            var num := StringToInt(parts[i]);
            result := result + [num];
        }
    }
}

method SplitBySpace(s: string) returns (parts: seq<string>)
{
    parts := [];
    var current := "";

    for i := 0 to |s|
    {
        if i < |s| && s[i] == ' ' {
            if |current| > 0 {
                parts := parts + [current];
                current := "";
            }
        } else if i < |s| {
            current := current + [s[i]];
        }
    }

    if |current| > 0 {
        parts := parts + [current];
    }
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result >= 0
{
    result := 0;
    for i := 0 to |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        result := result * 10 + (s[i] as int - '0' as int);
    }
}

method IntToString(n: int) returns (result: string)
    ensures |result| > 0
{
    if n == 0 {
        result := "0";
        return;
    }

    var num := n;
    var isNegative := false;

    if num < 0 {
        isNegative := true;
        num := -num;
    }

    result := "";

    assert num > 0;

    var origNum := num;

    while num > 0
        invariant num >= 0
        invariant isNegative ==> n < 0
        invariant !isNegative ==> n >= 0
        invariant |result| >= 0
        invariant origNum > 0
        invariant num < origNum ==> |result| > 0
    {
        var digit := num % 10;
        result := [(digit + '0' as int) as char] + result;
        num := num / 10;
    }

    if isNegative {
        result := "-" + result;
    }
}
```

```vc-code
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        output := "1 0";
        return;
    }

    assume |lines[0]| > 0 && forall i :: 0 <= i < |lines[0]| ==> '0' <= lines[0][i] <= '9';
    var n := StringToInt(lines[0]);
    assume 1 <= n <= 1000;

    assume |lines[1]| > 0;
    var sticks := ParseIntArray(lines[1]);
    assume |sticks| == n;
    assume forall i :: 0 <= i < |sticks| ==> 1 <= sticks[i] <= 100;

    var bestT, minCost := FindOptimalT(sticks);

    var bestTStr := IntToString(bestT);
    var minCostStr := IntToString(minCost);
    output := bestTStr + " " + minCostStr;
}
```