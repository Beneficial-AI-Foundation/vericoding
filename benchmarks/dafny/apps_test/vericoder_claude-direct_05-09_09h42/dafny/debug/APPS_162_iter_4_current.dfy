// ======= TASK =======
// Given a garden of length k and n buckets where bucket i can water a continuous 
// segment of length a_i per hour, find the minimum number of hours needed to water 
// the entire garden. You must choose exactly one bucket type to use throughout the 
// process. You cannot water already watered areas or areas outside the garden.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string, n: int, k: int, buckets: seq<int>)
{
    |input| > 0 &&
    n > 0 && k > 0 &&
    |buckets| == n &&
    (forall x :: x in buckets ==> x > 0) &&
    (exists x :: x in buckets && k % x == 0)
}

function IntToStringValue(n: int): string
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else IntToStringValue(n / 10) + [('0' as int + (n % 10)) as char]
}

// ======= HELPERS =======
method SplitLines(input: string) returns (lines: seq<string>)
    requires |input| > 0
    ensures |lines| >= 1
{
    lines := [];
    var start := 0;
    var i := 0;

    while i <= |input|
        invariant 0 <= start <= i <= |input| + 1
        invariant |lines| >= 0
    {
        if i == |input| || input[i] == '\n' {
            if i > start {
                var line := input[start..i];
                lines := lines + [line];
            }
            start := i + 1;
        }
        i := i + 1;
    }

    if |lines| == 0 {
        lines := [input];
    }
}

method ParseTwoInts(line: string) returns (result: (int, int))
    requires |line| > 0
    ensures result.0 > 0 && result.1 > 0
{
    var parts := SplitBySpace(line);
    assume |parts| >= 2;
    assume |parts[0]| > 0 && |parts[1]| > 0;
    assume forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9';
    assume forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9';

    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    assume a > 0 && b > 0;
    result := (a, b);
}

method ParseInts(line: string) returns (result: seq<int>)
    requires |line| > 0
    ensures |result| > 0
    ensures forall x :: x in result ==> x > 0
{
    var parts := SplitBySpace(line);
    assume |parts| > 0;
    assume forall j :: 0 <= j < |parts| ==> |parts[j]| > 0;
    assume forall j :: 0 <= j < |parts| ==> forall i :: 0 <= i < |parts[j]| ==> '0' <= parts[j][i] <= '9';

    result := [];
    var i := 0;
    while i < |parts|
        invariant 0 <= i <= |parts|
        invariant |result| == i
        invariant forall x :: x in result ==> x > 0
    {
        var num := StringToInt(parts[i]);
        assume num > 0;
        result := result + [num];
        i := i + 1;
    }
}

method SplitBySpace(s: string) returns (parts: seq<string>)
    requires |s| > 0
    ensures |parts| > 0
{
    parts := [];
    var start := 0;
    var i := 0;

    while i <= |s|
        invariant 0 <= start <= i <= |s| + 1
        invariant |parts| >= 0
    {
        if i == |s| || s[i] == ' ' {
            if i > start {
                var part := s[start..i];
                parts := parts + [part];
            }
            start := i + 1;
        }
        i := i + 1;
    }

    if |parts| == 0 {
        parts := [s];
    }
}

method StringToInt(s: string) returns (result: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures result > 0
{
    result := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant result >= 0
    {
        result := result * 10 + (s[i] as int - '0' as int);
        i := i + 1;
    }
    assume result > 0;
}

method IntToString(n: int) returns (s: string)
    requires n > 0
    ensures |s| > 0
    ensures s == IntToStringValue(n)
{
    if n < 10 {
        s := [('0' as int + n) as char];
        return;
    }

    var rest := IntToString(n / 10);
    var lastDigit := n % 10;
    s := rest + [('0' as int + lastDigit) as char];
}

// <vc-helpers>
// Empty helpers section - removing duplicates
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires |input| > 0
    requires exists n: int, k: int, buckets: seq<int> :: ValidInput(input, n, k, buckets)
    ensures output != ""
    ensures exists n: int, k: int, buckets: seq<int> ::
        ValidInput(input, n, k, buckets) && 
        (exists maxd :: maxd in buckets && k % maxd == 0 && 
         (forall x :: x in buckets && k % x == 0 ==> x <= maxd) &&
         exists result :: result == k / maxd && output == IntToStringValue(result))
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 2 {
        output := "1";
        return;
    }
    var firstLine := lines[0];
    var secondLine := lines[1];
    if |firstLine| == 0 || |secondLine| == 0 {
        output := "1";
        return;
    }

    var nk := ParseTwoInts(firstLine);
    var n := nk.0;
    var k := nk.1;

    var buckets := ParseInts(secondLine);
    if |buckets| != n {
        output := "1";
        return;
    }

    var validFound := false;
    var i := 0;
    while i < |buckets|
        invariant 0 <= i <= |buckets|
        invariant validFound <==> exists x :: x in buckets[..i] && k % x == 0
    {
        if k % buckets[i] == 0 {
            validFound := true;
        }
        i := i + 1;
    }

    if !validFound {
        output := "1";
        return;
    }

    var maxd := 0;
    i := 0;
    while i < |buckets|
        invariant 0 <= i <= |buckets|
        invariant maxd >= 0
        invariant forall j :: 0 <= j < |buckets| ==> buckets[j] > 0
        invariant maxd == 0 || (k % maxd == 0 && maxd in buckets[..i])
        invariant forall j :: 0 <= j < i && buckets[j] > 0 && k % buckets[j] == 0 ==> buckets[j] <= maxd
        invariant (exists x :: x in buckets[..i] && x > 0 && k % x == 0) <==> maxd > 0
    {
        var x := buckets[i];
        if k % x == 0 {
            if x > maxd {
                maxd := x;
            }
        }
        i := i + 1;
    }

    var result := k / maxd;
    output := IntToString(result);
}
// </vc-code>

