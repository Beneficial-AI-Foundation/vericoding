// <vc-preamble>
predicate ValidInputFormat(input: string)
{
    var lines := SplitByNewline(input);
    |lines| >= 3 && HasValidFirstLine(lines[0]) && HasValidElevationLine(lines[1]) &&
    HasValidRoadLines(lines[2..], GetN(lines[0]), GetM(lines[0])) &&
    GetN(lines[0]) > 0 && GetM(lines[0]) >= 0 &&
    |SplitBySpace(lines[1])| >= GetN(lines[0])
}

predicate HasValidFirstLine(line: string)
{
    var parts := SplitBySpace(line);
    |parts| == 2 && IsValidInt(parts[0]) && IsValidInt(parts[1]) &&
    ParseInt(parts[0]) >= 2 && ParseInt(parts[0]) <= 100000 &&
    ParseInt(parts[1]) >= 1 && ParseInt(parts[1]) <= 100000
}

predicate HasValidElevationLine(line: string)
{
    var parts := SplitBySpace(line);
    |parts| > 0 && (forall i | 0 <= i < |parts| :: 
        IsValidInt(parts[i]) && ParseInt(parts[i]) >= 1 && ParseInt(parts[i]) <= 1000000000)
}

predicate HasValidRoadLines(lines: seq<string>, N: int, M: int)
{
    |lines| >= M && forall i | 0 <= i < M :: HasValidRoadLine(lines[i], N)
}

predicate HasValidRoadLine(line: string, N: int)
{
    var parts := SplitBySpace(line);
    |parts| == 2 && IsValidInt(parts[0]) && IsValidInt(parts[1]) &&
    var a := ParseInt(parts[0]); var b := ParseInt(parts[1]);
    1 <= a <= N && 1 <= b <= N && a != b
}

function ParsedInput(input: string): (int, seq<int>, seq<(int, int)>)
    requires ValidInputFormat(input)
{
    var lines := SplitByNewline(input);
    var N := GetN(lines[0]);
    var M := GetM(lines[0]);
    var elevations := GetElevations(lines[1], N);
    var roads := GetRoads(lines[2..], M);
    (N, elevations, roads)
}

function CountGoodObservatories(parsed: (int, seq<int>, seq<(int, int)>)): int
    requires parsed.0 > 0
    requires |parsed.1| == parsed.0
    requires forall i | 0 <= i < |parsed.2| :: 1 <= parsed.2[i].0 <= parsed.0 && 1 <= parsed.2[i].1 <= parsed.0
{
    var (N, elevations, roads) := parsed;
    var maxNeighborElevations := ComputeMaxNeighborElevations(N, elevations, roads);
    CountObservatoriesWithHigherElevation(elevations, maxNeighborElevations)
}

function GetN(line: string): int
    requires HasValidFirstLine(line)
{
    var parts := SplitBySpace(line);
    ParseInt(parts[0])
}

function GetM(line: string): int
    requires HasValidFirstLine(line)
{
    var parts := SplitBySpace(line);
    ParseInt(parts[1])
}

function GetElevations(line: string, N: int): seq<int>
    requires N >= 0
    requires |SplitBySpace(line)| >= N
    ensures |GetElevations(line, N)| == N
{
    var parts := SplitBySpace(line);
    seq(N, i requires 0 <= i < N => ParseInt(parts[i]))
}

function GetRoads(lines: seq<string>, M: int): seq<(int, int)>
    requires M >= 0
    requires |lines| >= M
    requires forall i | 0 <= i < M :: |SplitBySpace(lines[i])| >= 2
    ensures |GetRoads(lines, M)| == M
{
    seq(M, i requires 0 <= i < M =>
        var parts := SplitBySpace(lines[i]);
        (ParseInt(parts[0]), ParseInt(parts[1]))
    )
}

function ComputeMaxNeighborElevations(N: int, elevations: seq<int>, roads: seq<(int, int)>): seq<int>
    requires N > 0
    requires |elevations| == N
    requires forall i | 0 <= i < |roads| :: 1 <= roads[i].0 <= N && 1 <= roads[i].1 <= N
    ensures |ComputeMaxNeighborElevations(N, elevations, roads)| == N
{
    var initial := seq(N, i => 0);
    ComputeMaxNeighborElevationsHelper(initial, elevations, roads)
}

function ComputeMaxNeighborElevationsHelper(current: seq<int>, elevations: seq<int>, roads: seq<(int, int)>): seq<int>
    requires |current| == |elevations|
    requires |current| > 0
    requires forall i | 0 <= i < |roads| :: 1 <= roads[i].0 <= |current| && 1 <= roads[i].1 <= |current|
    ensures |ComputeMaxNeighborElevationsHelper(current, elevations, roads)| == |current|
    decreases |roads|
{
    if |roads| == 0 then current
    else
        var (a, b) := roads[0];
        var updated := current[a-1 := Max(elevations[b-1], current[a-1])]
                              [b-1 := Max(current[b-1], elevations[a-1])];
        ComputeMaxNeighborElevationsHelper(updated, elevations, roads[1..])
}

function CountObservatoriesWithHigherElevation(elevations: seq<int>, maxNeighborElevations: seq<int>): int
    requires |elevations| == |maxNeighborElevations|
{
    if |elevations| == 0 then 0
    else
        (if elevations[0] > maxNeighborElevations[0] then 1 else 0) +
        CountObservatoriesWithHigherElevation(elevations[1..], maxNeighborElevations[1..])
}

predicate IsValidInt(s: string)
{
    |s| > 0
}

function SplitByNewline(s: string): seq<string>
{
    []
}

function SplitBySpace(s: string): seq<string>
{
    []
}

function ParseInt(s: string): int
{
    0
}

function IntToString(n: int): string
{
    ""
}
// </vc-preamble>

// <vc-helpers>
function Max(a: int, b: int): int
{
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInputFormat(input)
    ensures |result| > 0
    ensures result == IntToString(CountGoodObservatories(ParsedInput(input)))
    ensures CountGoodObservatories(ParsedInput(input)) >= 0
    ensures CountGoodObservatories(ParsedInput(input)) <= ParsedInput(input).0
// </vc-spec>
// <vc-code>
{
    var lines := SplitByNewline(input);
    var firstLine := SplitBySpace(lines[0]);
    var N := ParseInt(firstLine[0]);
    var M := ParseInt(firstLine[1]);

    var secondLine := SplitBySpace(lines[1]);
    var high := new int[N];
    for i := 0 to N {
        high[i] := ParseInt(secondLine[i]);
    }

    var ans := new int[N];
    for i := 0 to N {
        ans[i] := 0;
    }

    for i := 0 to M {
        var tmpCall1 := SplitBySpace(lines[2 + i]);
        var roadLine := tmpCall1;
        var a := ParseInt(roadLine[0]);
        var b := ParseInt(roadLine[1]);

        ans[a-1] := Max(high[b-1], ans[a-1]);
        ans[b-1] := Max(ans[b-1], high[a-1]);
    }

    var cnt := 0;
    for j := 0 to N {
        if ans[j] < high[j] {
            cnt := cnt + 1;
        }
    }

    result := IntToString(cnt);
}
// </vc-code>
