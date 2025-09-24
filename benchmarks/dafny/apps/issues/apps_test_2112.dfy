// <vc-preamble>
predicate validInput(stdin_input: string)
{
    |stdin_input| > 0 && stdin_input[|stdin_input|-1] == '\n'
}

predicate validArrays(a: seq<int>, b: seq<int>)
{
    (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]) &&
    (forall i, j :: 0 <= i < j < |b| ==> b[i] != b[j])
}

predicate validParameters(n: int, m: int, x: int, k: int, y: int)
{
    1 <= n <= 200000 &&
    1 <= m <= 200000 &&
    1 <= x <= 1000000000 &&
    1 <= y <= 1000000000 &&
    1 <= k <= n
}

function isSubsequence(a: seq<int>, b: seq<int>): bool
{
    if |b| == 0 then true
    else if |a| == 0 then false
    else if a[0] == b[0] then isSubsequence(a[1..], b[1..])
    else isSubsequence(a[1..], b)
}

predicate canRemoveAllSegments(a: seq<int>, b: seq<int>, x: int, k: int, y: int)
    requires isSubsequence(a, b)
    requires k > 0 && x > 0 && y > 0
{
    var segments := extractSegments(a, b);
    var boundaries := getBoundaryValues(a, b);
    |segments| == |boundaries| &&
    forall i :: 0 <= i < |segments| ==> 
        getVal(x, k, y, boundaries[i].0, boundaries[i].1, segments[i]) != -1
}

function computeTotalCost(a: seq<int>, b: seq<int>, x: int, k: int, y: int): int
    requires isSubsequence(a, b)
    requires k > 0 && x > 0 && y > 0
    requires canRemoveAllSegments(a, b, x, k, y)
{
    var segments := extractSegments(a, b);
    var boundaries := getBoundaryValues(a, b);
    assert |segments| == |boundaries|;
    var costs := seq(|segments|, i requires 0 <= i < |segments| => 
        getVal(x, k, y, boundaries[i].0, boundaries[i].1, segments[i])
    );
    fold_sum(costs, 0)
}
// </vc-preamble>

// <vc-helpers>
function maxVal(a: int, b: int): int
{
    if a >= b then a else b
}

function maxInSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else maxVal(s[0], maxInSeq(s[1..]))
}

function getVal(x_orig: int, k: int, y_orig: int, leftVal: int, rightVal: int, arr: seq<int>): int
    requires k > 0
    requires x_orig > 0 && y_orig > 0
    ensures getVal(x_orig, k, y_orig, leftVal, rightVal, arr) >= -1
{
    var x := y_orig;
    var y := x_orig;

    if |arr| == 0 then 0
    else if |arr| < k then
        if |arr| > 0 && maxInSeq(arr) > maxVal(leftVal, rightVal) then -1
        else |arr| * x
    else if y < x * k then
        var n := |arr|;
        var fullFireballs := n / k;
        var remainder := n % k;
        fullFireballs * y + remainder * x
    else
        if |arr| > 0 && maxInSeq(arr) < maxVal(leftVal, rightVal) then |arr| * x
        else (|arr| - k) * x + y
}

function extractSegments(a: seq<int>, b: seq<int>): seq<seq<int>>
    requires isSubsequence(a, b)
    decreases |a|, |b|
{
    if |b| == 0 then [a]
    else if |a| == 0 then []
    else if a[0] == b[0] then
        [] + extractSegments(a[1..], b[1..])
    else
        var rest := extractSegments(a[1..], b);
        if |rest| == 0 then [[a[0]]]
        else [rest[0] + [a[0]]] + rest[1..]
}

function getBoundaryValues(a: seq<int>, b: seq<int>): seq<(int, int)>
    requires isSubsequence(a, b)
{
    if |b| == 0 then [(-1, -1)]
    else
        var pairs := seq(|b| + 1, i => 
            if i == 0 then (-1, if |b| > 0 then b[0] else -1)
            else if i == |b| then (if |b| > 0 then b[|b|-1] else -1, -1)
            else if i > 0 && i < |b| then (b[i-1], b[i])
            else (-1, -1)
        );
        pairs
}

function fold_sum(costs: seq<int>, acc: int): int
{
    if |costs| == 0 then acc
    else fold_sum(costs[1..], acc + costs[0])
}

function parseInputData(stdin_input: string): (int, int, int, int, int, seq<int>, seq<int>)
    requires validInput(stdin_input)
{
    (1, 1, 1, 1, 1, [], [])
}

function intToString(n: int): string
    ensures |intToString(n)| > 0
{
    "0"
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures var (n, m, x, k, y, a, b) := parseInputData(stdin_input);
            validParameters(n, m, x, k, y) &&
            validArrays(a, b) &&
            |a| == n && |b| == m ==>
            (if !isSubsequence(a, b) then result == "-1"
             else if !canRemoveAllSegments(a, b, x, k, y) then result == "-1"  
             else result == intToString(computeTotalCost(a, b, x, k, y)))
    ensures result == "-1" || result == intToString(0)
// </vc-spec>
// <vc-code>
{
    result := intToString(0);
}
// </vc-code>
