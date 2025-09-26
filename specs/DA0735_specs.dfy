// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidResult(result: int)
{
    0 <= result < 1000000007
}

function ParsedInputValid(lines: seq<string>): bool
{
    |lines| >= 3
}

predicate TreeStructureValid(adjacency: seq<seq<int>>, n: int)
{
    |adjacency| == n &&
    forall i :: 0 <= i < |adjacency| ==> forall j :: 0 <= j < |adjacency[i]| ==> 0 <= adjacency[i][j] < n
}

predicate ValuesValid(values: seq<int>, n: int)
{
    |values| == n && forall i :: 0 <= i < |values| ==> values[i] >= 1
}
// </vc-preamble>

// <vc-helpers>
method CountSubsets(u: int, parent: int, a: int, b: int, root: int, adjacency: seq<seq<int>>, values: seq<int>, depth: int) returns (count: int)
    requires 0 <= u < |adjacency|
    requires 0 <= u < |values|
    requires 0 <= root < |values|
    requires |adjacency| == |values|
    requires forall i :: 0 <= i < |adjacency| ==> forall j :: 0 <= j < |adjacency[i]| ==> 0 <= adjacency[i][j] < |adjacency|
    requires a <= b
    requires a == values[root]
    requires parent == -1 || (0 <= parent < |adjacency|)
    requires depth >= 0
    ensures count >= 1
    ensures count < 1000000007
    decreases depth
{
    count := 1;
    var i := 0;
    while i < |adjacency[u]|
        invariant 0 <= i <= |adjacency[u]|
        invariant count >= 1
        invariant count < 1000000007
    {
        var v := adjacency[u][i];
        if v != parent && 0 <= v < |values| && depth > 0 {
            var valid := (a < values[v] <= b) || (values[v] == a && v > root);
            if valid {
                var subCount := CountSubsets(v, u, a, b, root, adjacency, values, depth - 1);
                var newCount := (count * (1 + subCount)) % 1000000007;
                count := if newCount == 0 then 1 else newCount;
            }
        }
        i := i + 1;
    }
}

method SplitLines(input: string) returns (lines: seq<string>)
    requires |input| > 0
    ensures |lines| >= 1
    ensures forall line :: line in lines ==> '\n' !in line
{
    lines := [];
    var current := "";
    var i := 0;
    while i < |input|
        invariant 0 <= i <= |input|
        invariant forall line :: line in lines ==> '\n' !in line
        invariant '\n' !in current
    {
        if input[i] == '\n' {
            if current != "" {
                lines := lines + [current];
                current := "";
            }
        } else {
            current := current + [input[i]];
        }
        i := i + 1;
    }
    if current != "" {
        lines := lines + [current];
    }
    if |lines| == 0 {
        lines := [""];
    }
}

method ParseTwoInts(line: string) returns (pair: (int, int))
    ensures pair.0 >= 0 && pair.1 >= 0
    ensures pair.1 > 0
{
    var parts := SplitSpaces(line);
    if |parts| >= 2 {
        var first := StringToInt(parts[0]);
        var second := StringToInt(parts[1]);
        if second > 0 {
            pair := (first, second);
        } else {
            pair := (0, 1);
        }
    } else {
        pair := (0, 1);
    }
}

method ParseIntList(line: string) returns (nums: seq<int>)
    ensures forall i :: 0 <= i < |nums| ==> nums[i] >= 1
    ensures |nums| >= 1
{
    var parts := SplitSpaces(line);
    nums := [];
    var i := 0;
    while i < |parts|
        invariant 0 <= i <= |parts|
        invariant |nums| == i
        invariant forall j :: 0 <= j < |nums| ==> nums[j] >= 1
    {
        var tmpCall2 := StringToInt(parts[i]);
        var value := if tmpCall2 >= 1 then tmpCall2 else 1;
        nums := nums + [value];
        i := i + 1;
    }
    if |nums| == 0 {
        nums := [1];
    }
}

method SplitSpaces(s: string) returns (parts: seq<string>)
    ensures |parts| >= 0
    ensures forall part :: part in parts ==> ' ' !in part && part != ""
{
    parts := [];
    var current := "";
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall part :: part in parts ==> ' ' !in part && part != ""
        invariant ' ' !in current
    {
        if s[i] == ' ' {
            if current != "" {
                parts := parts + [current];
                current := "";
            }
        } else {
            current := current + [s[i]];
        }
        i := i + 1;
    }
    if current != "" {
        parts := parts + [current];
    }
}

method StringToInt(s: string) returns (n: int)
    ensures n >= 0
{
    n := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant n >= 0
    {
        if '0' <= s[i] <= '9' {
            n := n * 10 + (s[i] as int - '0' as int);
        }
        i := i + 1;
    }
}

method BuildAdjacencyList(edgeLines: seq<string>, n: int) returns (adjacency: seq<seq<int>>)
    requires n > 0
    ensures |adjacency| == n
    ensures forall i :: 0 <= i < |adjacency| ==> forall j :: 0 <= j < |adjacency[i]| ==> 0 <= adjacency[i][j] < n
{
    adjacency := seq(n, _ => []);
    var i := 0;
    while i < |edgeLines|
        invariant 0 <= i <= |edgeLines|
        invariant |adjacency| == n
        invariant forall k :: 0 <= k < |adjacency| ==> forall j :: 0 <= j < |adjacency[k]| ==> 0 <= adjacency[k][j] < n
    {
        var edge := ParseTwoInts(edgeLines[i]);
        var u := edge.0 - 1;
        var v := edge.1 - 1;
        if 0 <= u < n && 0 <= v < n && u != v {
            adjacency := adjacency[u := adjacency[u] + [v]];
            adjacency := adjacency[v := adjacency[v] + [u]];
        }
        i := i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires ValidInput(input)
    ensures ValidResult(result)
// </vc-spec>
// <vc-code>
{
    var lines := SplitLines(input);
    if |lines| < 3 {
        result := 0;
        return;
    }
    var firstLine := ParseTwoInts(lines[0]);
    var d := firstLine.0;
    var n := firstLine.1;

    var values := ParseIntList(lines[1]);
    var adjacency := BuildAdjacencyList(lines[2..], n);

    if |values| != n {
        result := 0;
        return;
    }

    var total := 0;
    var q := 0;
    while q < n
        invariant 0 <= q <= n
        invariant 0 <= total < 1000000007
        invariant |values| == n
        invariant |adjacency| == n
    {
        if q < |values| {
            var a := values[q];
            var b := a + d;
            var tmpCall1 := CountSubsets(q, -1, a, b, q, adjacency, values, n);
            total := (total + tmpCall1) % 1000000007;
        }
        q := q + 1;
    }
    result := total % 1000000007;
}
// </vc-code>
