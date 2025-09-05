// ======= TASK =======
// Find the position (x, y) after making n moves along a spiral path on a hexagonal grid starting from (0,0).
// The spiral moves outward in hexagonal rings, where each ring consists of 6 sides following a specific directional pattern.

// ======= SPEC REQUIREMENTS =======
predicate ValidInput(input: string)
{
    |input| > 0 &&
    (forall i :: 0 <= i < |input| ==> '0' <= input[i] <= '9' || input[i] == ' ' || input[i] == '\t' || input[i] == '\n' || input[i] == '\r' || input[i] == '-') &&
    ParseInt(Trim(input)) >= 0
}

// ======= HELPERS =======
function Trim(s: string): string
{
    if |s| == 0 then ""
    else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' then Trim(s[1..])
    else if s[|s|-1] == ' ' || s[|s|-1] == '\t' || s[|s|-1] == '\n' || s[|s|-1] == '\r' then Trim(s[..|s|-1])
    else s
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -ParseIntHelper(s[1..])
    else ParseIntHelper(s)
}

function ParseIntHelper(s: string): int
{
    if |s| == 0 then 0
    else ParseIntHelper(s[..|s|-1]) * 10 + (s[|s|-1] as int - '0' as int)
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [('0' as int + n % 10) as char]
}

// <vc-helpers>
function HexagonalSpiralPosition(n: int): (int, int)
    requires n >= 0
    ensures n == 0 ==> HexagonalSpiralPosition(n) == (0, 0)
{
    if n == 0 then (0, 0)
    else
        var ringInfo := HexagonalSpiralHelper(n);
        ComputeFinalPositionFromRing(ringInfo.1, ringInfo.0)
}

function HexagonalSpiralHelper(n: int): (int, int)
    requires n >= 0
    ensures HexagonalSpiralHelper(n).0 >= 0
    ensures HexagonalSpiralHelper(n).1 >= 0
{
    if n == 0 then (0, 0)
    else 
        ComputeRingHelper(n, 1, 1)
}

function ComputeRingHelper(n: int, k: int, totalInPrevRings: int): (int, int)
    requires n >= 0
    requires k >= 1
    requires totalInPrevRings >= 1
    requires totalInPrevRings == 1 + 3 * (k - 1) * k
    requires totalInPrevRings <= n
    ensures ComputeRingHelper(n, k, totalInPrevRings).0 >= 0
    ensures ComputeRingHelper(n, k, totalInPrevRings).1 >= 0
    decreases n - totalInPrevRings
{
    if totalInPrevRings + 6 * k <= n then
        ComputeRingHelper(n, k + 1, totalInPrevRings + 6 * k)
    else
        (n - totalInPrevRings, k)
}

function ComputeFinalPositionFromRing(k: int, remaining: int): (int, int)
    requires remaining >= 0
    requires k >= 0
    ensures k == 0 && remaining == 0 ==> ComputeFinalPositionFromRing(k, remaining) == (0, 0)
{
    if k == 0 && remaining == 0 then (0, 0)
    else
        var x := k;
        var y := -2 * k;
        var d := [k + 1, k, k + 1, k + 1, k + 1, k + 1];
        var dx := [1, -1, -2, -1, 1, 2];
        var dy := [2, 2, 0, -2, -2, 0];
        ComputeFinalPositionHelper(remaining, x, y, d, dx, dy, 0)
}

function ComputeFinalPositionHelper(remaining: int, x: int, y: int, d: seq<int>, dx: seq<int>, dy: seq<int>, i: int): (int, int)
    requires remaining >= 0
    requires |d| == 6 && |dx| == 6 && |dy| == 6
    requires 0 <= i <= 6
    requires dx == [1, -1, -2, -1, 1, 2]
    requires dy == [2, 2, 0, -2, -2, 0]
    decreases remaining + (6 - i)
{
    if i >= 6 || remaining == 0 then (x, y)
    else
        var steps := if d[i] <= remaining then d[i] else remaining;
        var newX := x + steps * dx[i];
        var newY := y + steps * dy[i];
        var newRemaining := remaining - steps;
        ComputeFinalPositionHelper(newRemaining, newX, newY, d, dx, dy, i + 1)
}

method findRing(n: int) returns (remaining: int, k: int)
    requires n >= 0
    ensures k >= 0
    ensures remaining >= 0
    ensures n == 0 ==> k == 0 && remaining == 0
{
    if n == 0 {
        remaining := 0;
        k := 0;
        return;
    }

    k := 1;
    var totalInPrevRings := 1;

    while totalInPrevRings + 6 * k <= n
        invariant k >= 1
        invariant totalInPrevRings >= 1
        invariant totalInPrevRings == 1 + 3 * (k - 1) * k
        invariant totalInPrevRings <= n
    {
        totalInPrevRings := totalInPrevRings + 6 * k;
        k := k + 1;
    }

    remaining := n - totalInPrevRings;
}
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures |output| > 0
    ensures (exists x, y :: output == IntToString(x) + " " + IntToString(y) && 
            HexagonalSpiralPosition(ParseInt(Trim(input))) == (x, y))
// </vc-spec>
// <vc-code>
{
    var n := ParseInt(Trim(input));
    var pos := HexagonalSpiralPosition(n);
    var tmpCall1 := IntToString(pos.0);
    var tmpCall2 := IntToString(pos.1);
    output := tmpCall1 + " " + tmpCall2;
}
// </vc-code>

