// <vc-preamble>
predicate validInputFormat(input: string)
{
    var lines := splitLinesFunc(input);
    |lines| >= 2 && 
    isValidInteger(lines[0]) &&
    (var n := parseIntFunc(lines[0]);
     n >= 2 && n <= 100000 &&
     isValidIntegerArray(lines[1], n))
}

predicate isValidInteger(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate isValidIntegerArray(s: string, expectedCount: int)
{
    expectedCount > 0 && |s| > 0
}

function maxGcdAfterRemoval(a: seq<int>): int
    requires |a| >= 2
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures maxGcdAfterRemoval(a) >= 1
{
    maxGcdAfterRemovalHelper(a, 0, 1)
}

function maxGcdAfterRemovalHelper(a: seq<int>, i: int, maxGcd: int): int
    requires |a| >= 2
    requires forall j :: 0 <= j < |a| ==> a[j] >= 1
    requires 0 <= i <= |a|
    requires maxGcd >= 1
    ensures maxGcdAfterRemovalHelper(a, i, maxGcd) >= 1
    decreases |a| - i
{
    if i >= |a| then maxGcd
    else 
        var gcdExceptI := gcdOfAllExcept(a, i);
        var newMaxGcd := if gcdExceptI > maxGcd then gcdExceptI else maxGcd;
        maxGcdAfterRemovalHelper(a, i + 1, newMaxGcd)
}

function gcdOfAllExcept(a: seq<int>, skipIndex: int): int
    requires |a| >= 2
    requires 0 <= skipIndex < |a|
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures gcdOfAllExcept(a, skipIndex) >= 1
{
    var filtered := buildFilteredSeq(a, skipIndex);
    gcdOfSequence(filtered)
}

function buildFilteredSeq(a: seq<int>, skipIndex: int): seq<int>
    requires |a| >= 2
    requires 0 <= skipIndex < |a|
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures |buildFilteredSeq(a, skipIndex)| == |a| - 1
    ensures |buildFilteredSeq(a, skipIndex)| >= 1
    ensures forall i :: 0 <= i < |buildFilteredSeq(a, skipIndex)| ==> 
        buildFilteredSeq(a, skipIndex)[i] >= 1
{
    a[..skipIndex] + a[skipIndex+1..]
}

function gcdOfSequence(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures gcdOfSequence(s) >= 1
    decreases |s|
{
    if |s| == 1 then s[0]
    else 
        var restGcd := gcdOfSequence(s[1..]);
        gcd(s[0], restGcd)
}

function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
    ensures a == 0 || gcd(a, b) <= a
    ensures b == 0 || gcd(a, b) <= b
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function splitLinesFunc(input: string): seq<string>
{
    ["", ""]
}

function parseIntFunc(s: string): int
    requires isValidInteger(s)
    ensures parseIntFunc(s) >= 0
{
    0
}

function parseIntArrayFunc(s: string, n: int): seq<int>
    requires n >= 0
    ensures |parseIntArrayFunc(s, n)| == n
    ensures forall i :: 0 <= i < |parseIntArrayFunc(s, n)| ==> parseIntArrayFunc(s, n)[i] >= 1
{
    seq(n, _ => 1)
}

function intToStringFunc(n: int): string
    requires n >= 0
    ensures |intToStringFunc(n)| > 0
    ensures n == 0 ==> intToStringFunc(n) == "0"
    ensures n > 0 ==> |intToStringFunc(n)| >= 1
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else intToStringFunc(n / 10) + intToStringFunc(n % 10)
}
// </vc-preamble>

// <vc-helpers>
method splitLines(input: string) returns (lines: seq<string>)
    ensures |lines| >= 0
    ensures forall i :: 0 <= i < |lines| ==> |lines[i]| >= 0
{
    lines := splitLinesFunc(input);
}

method parseInt(s: string) returns (n: int)
    requires |s| > 0
    ensures n >= 0
{
    n := if isValidInteger(s) then parseIntFunc(s) else 0;
}

method parseIntArray(s: string, expectedLen: int) returns (arr: seq<int>)
    requires expectedLen >= 0
    ensures |arr| <= expectedLen
    ensures forall i :: 0 <= i < |arr| ==> arr[i] > 0
{
    if isValidIntegerArray(s, expectedLen) {
        arr := parseIntArrayFunc(s, expectedLen);
    } else {
        arr := [];
    }
}

method intToString(n: int) returns (s: string)
    requires n >= 0
    ensures |s| > 0
    ensures n == 0 ==> s == "0"
    ensures n > 0 ==> |s| >= 1
{
    s := intToStringFunc(n);
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInputFormat(stdin_input)
    ensures |result| > 0
    ensures exists ans: int :: ans >= 1 && result == intToStringFunc(ans) + "\n"
    ensures validInputFormat(stdin_input) ==> 
        (var lines := splitLinesFunc(stdin_input);
         var n := parseIntFunc(lines[0]);
         var a := parseIntArrayFunc(lines[1], n);
         result == intToStringFunc(maxGcdAfterRemoval(a)) + "\n")
// </vc-spec>
// <vc-code>
{
    var lines := splitLines(stdin_input);
    if |lines| < 2 {
        result := "1\n";
        return;
    }

    var n := parseInt(lines[0]);
    if n < 2 {
        result := "1\n";
        return;
    }

    var a := parseIntArray(lines[1], n);
    if |a| != n {
        result := "1\n";
        return;
    }

    var l := new int[n+2];
    l[0] := 0;
    l[1] := a[0];
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant forall k :: 1 <= k <= i ==> l[k] > 0
    {
        l[i+1] := gcd(l[i], a[i]);
        i := i + 1;
    }

    var r := new int[n+2];
    r[n+1] := 0;
    r[n] := a[n-1];
    i := 1;
    while i < n
        invariant 1 <= i <= n-1
        invariant forall k :: n-i+1 <= k <= n ==> r[k] > 0
    {
        r[n-i] := gcd(r[n-i+1], a[n-1-i]);
        i := i + 1;
    }

    var ans := 0;
    i := 1;
    while i <= n
        invariant 1 <= i <= n+1
        invariant ans >= 0
    {
        var leftGcd := if i-1 >= 1 then l[i-1] else 0;
        var rightGcd := if i+1 <= n then r[i+1] else 0;
        var currentGcd := if leftGcd == 0 then rightGcd 
                         else if rightGcd == 0 then leftGcd
                         else gcd(leftGcd, rightGcd);
        if currentGcd > ans {
            ans := currentGcd;
        }
        i := i + 1;
    }

    var ansStr := intToString(ans);
    result := ansStr + "\n";
}
// </vc-code>
