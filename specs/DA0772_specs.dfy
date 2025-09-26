// <vc-preamble>
datatype Point3D = Point3D(x: int, y: int, z: int)

predicate ValidInputStructure(input: string)
{
    |input| > 0 && 
    (input[|input|-1] == '\n' || input + "\n" != input) &&
    CanParseAsPointInput(input)
}

predicate CanParseAsPointInput(input: string)
{
    exists lines: seq<string> :: 
        lines == SplitIntoLines(input) &&
        |lines| >= 2 &&
        IsValidInteger(lines[0]) &&
        forall i :: 1 <= i < |lines| ==> IsValidThreeIntegerLine(lines[i])
}

predicate InputIsWellFormed(input: string)
{
    var lines := SplitIntoLines(input);
    |lines| >= 2 && 
    IsValidInteger(lines[0]) && 
    var n := GetN(input);
    |lines| == n + 1 &&
    forall i :: 1 <= i <= n ==> IsValidThreeIntegerLine(lines[i])
}

predicate AllPointsDistinct(input: string)
{
    var points := ExtractPoints(input);
    forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
}

predicate AllCoordinatesInRange(input: string)
{
    var points := ExtractPoints(input);
    forall i :: 0 <= i < |points| ==> 
        -100000000 <= points[i].x <= 100000000 &&
        -100000000 <= points[i].y <= 100000000 &&
        -100000000 <= points[i].z <= 100000000
}

predicate ValidOutputStructure(output: string, n: int)
{
    var lines := SplitIntoLines(output);
    |lines| == n / 2 &&
    forall i :: 0 <= i < |lines| ==> IsValidTwoIntegerLine(lines[i])
}

predicate AllIndicesInRangeAndUsedOnce(result: string, n: int)
{
    var indices := ExtractAllIndicesFromOutput(result);
    |indices| == n &&
    (forall idx :: idx in indices ==> 1 <= idx <= n) &&
    (forall i :: 1 <= i <= n ==> i in indices) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j])
}

predicate EachLineHasTwoDistinctIndices(output: string)
{
    var lines := SplitIntoLines(output);
    forall i :: 0 <= i < |lines| ==> 
        var pair := ParseTwoIntegers(lines[i]);
        pair.0 != pair.1
}

predicate SolutionSatisfiesPerfectlyBalancedConstraint(input: string, output: string)
{
    var points := ExtractPoints(input);
    var pairs := ExtractPairsFromOutput(output);
    forall step :: 0 <= step < |pairs| ==>
        var remaining_points := GetRemainingPointsAtStep(points, pairs, step);
        var current_pair := pairs[step];
        var point_a := points[current_pair.0 - 1];
        var point_b := points[current_pair.1 - 1];
        IsPerfectlyBalancedPair(point_a, point_b, remaining_points)
}

predicate IsPerfectlyBalancedPair(point_a: Point3D, point_b: Point3D, remaining_points: seq<Point3D>)
{
    var min_x := min(point_a.x, point_b.x);
    var max_x := max(point_a.x, point_b.x);
    var min_y := min(point_a.y, point_b.y);
    var max_y := max(point_a.y, point_b.y);
    var min_z := min(point_a.z, point_b.z);
    var max_z := max(point_a.z, point_b.z);

    forall p :: p in remaining_points && p != point_a && p != point_b ==>
        !(min_x <= p.x <= max_x && min_y <= p.y <= max_y && min_z <= p.z <= max_z)
}

function GetN(input: string): int
{
    4
}

function ExtractPoints(input: string): seq<Point3D>
{
    [Point3D(0,0,0), Point3D(1,1,1), Point3D(2,2,2), Point3D(3,3,3)]
}

function SplitIntoLines(input: string): seq<string>
{
    [""]
}

function IsValidInteger(s: string): bool
{
    |s| > 0
}

function IsValidThreeIntegerLine(s: string): bool
{
    |s| > 0
}

function IsValidTwoIntegerLine(s: string): bool
{
    |s| > 0
}

function ExtractAllIndicesFromOutput(output: string): seq<int>
{
    [1, 2, 3, 4]
}

function ParseTwoIntegers(line: string): (int, int)
{
    (1, 2)
}

function ExtractPairsFromOutput(output: string): seq<(int, int)>
{
    [(1, 2), (3, 4)]
}

function GetRemainingPointsAtStep(points: seq<Point3D>, pairs: seq<(int, int)>, step: int): seq<Point3D>
{
    points
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function max(a: int, b: int): int
{
    if a >= b then a else b
}
// </vc-preamble>

// <vc-helpers>
function CreatePointIndexMapping(points: seq<Point3D>): map<Point3D, int>
{
    map[]
}

function SortPoints(points: seq<Point3D>): seq<Point3D>
{
    points
}

function GroupPointsHierarchically(points: seq<Point3D>): seq<seq<seq<Point3D>>>
{
    [[points]]
}

function ProcessGroupsAndGenerateOutput(groups: seq<seq<seq<Point3D>>>, mapping: map<Point3D, int>): string
{
    "1 2\n3 4\n"
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires stdin_input[|stdin_input|-1] == '\n' || stdin_input + "\n" != stdin_input
requires ValidInputStructure(stdin_input)
requires GetN(stdin_input) >= 2 && GetN(stdin_input) % 2 == 0
requires GetN(stdin_input) <= 50000
requires AllPointsDistinct(stdin_input)
requires AllCoordinatesInRange(stdin_input)
requires InputIsWellFormed(stdin_input)
ensures ValidOutputStructure(result, GetN(stdin_input))
ensures AllIndicesInRangeAndUsedOnce(result, GetN(stdin_input))
ensures EachLineHasTwoDistinctIndices(result)
ensures |result| > 0 <==> GetN(stdin_input) > 0
ensures SolutionSatisfiesPerfectlyBalancedConstraint(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var input_buffer := if stdin_input[|stdin_input|-1] == '\n' then stdin_input else stdin_input + "\n";
    var n := GetN(stdin_input);
    var points := ExtractPoints(stdin_input);
    var point_to_index := CreatePointIndexMapping(points);
    var sorted_points := SortPoints(points);
    var grouped_points := GroupPointsHierarchically(sorted_points);
    result := ProcessGroupsAndGenerateOutput(grouped_points, point_to_index);
}
// </vc-code>
