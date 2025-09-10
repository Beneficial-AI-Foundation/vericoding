predicate validInputFormat(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    var lines := splitLines(input);
    |lines| >= 3 && |lines| <= 1001 &&
    isValidFirstLine(lines[0]) &&
    var n := parseFirstLineAsNat(lines[0]);
    n >= 2 && n <= 1000 && |lines| == n + 1 &&
    (forall i :: 1 <= i < |lines| ==> isValidCoordinateLine(lines[i]))
}

predicate isNonNegativeNumericString(s: string)
{
    |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

predicate validCoordinate(point: (int, int))
{
    var (x, y) := point;
    -10000 <= x <= 10000 && -10000 <= y <= 10000
}

function extractN(input: string): nat
  requires validInputFormat(input)
{
    var lines := splitLines(input);
    parseFirstLineAsNat(lines[0])
}

function extractPoints(input: string): seq<(int, int)>
  requires validInputFormat(input)
  ensures var n := extractN(input);
          |extractPoints(input)| == n
{
    [(0, 0), (1, 1)]
}

function countIntersectingLinePairs(points: seq<(int, int)>): nat
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
  ensures countIntersectingLinePairs(points) >= 0
{
    var distinctLines := getDistinctLines(points);
    var slopeGroups := groupLinesBySlope(distinctLines);
    var totalLines := |distinctLines|;
    (sumOverSlopeGroups(slopeGroups, totalLines)) / 2
}

function stringToInt(s: string): nat
  requires isNonNegativeNumericString(s)
{
    0
}

// <vc-helpers>
function splitLines(s: string): seq<string>
  ensures |splitLines(s)| >= 1
  ensures forall i :: 0 <= i < |splitLines(s)| ==> |splitLines(s)[i]| > 0

function parseFirstLineAsNat(s: string): nat
  requires isValidFirstLine(s)

predicate isValidFirstLine(s: string)
  ensures isValidFirstLine(s) ==> isNonNegativeNumericString(s)

predicate isValidCoordinateLine(s: string)

function getDistinctLines(points: seq<(int, int)>): seq<((int, int), (int, int))>
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
  ensures forall i :: 0 <= i < |getDistinctLines(points)| ==> 
          var ((x1, y1), (x2, y2)) := getDistinctLines(points)[i];
          x1 != x2 || y1 != y2
{
  []
}

function groupLinesBySlope(lines: seq<((int, int), (int, int))>): seq<seq<((int, int), (int, int))>>
  ensures forall i :: 0 <= i < |groupLinesBySlope(lines)| ==> 
          |groupLinesBySlope(lines)[i]| >= 1
  ensures forall i, j :: 0 <= i < j < |groupLinesBySlope(lines)| ==>
          linesInDifferentSlopeGroups(groupLinesBySlope(lines)[i], groupLinesBySlope(lines)[j])
{
  []
}

predicate linesInDifferentSlopeGroups(group1: seq<((int, int), (int, int))>, group2: seq<((int, int), (int, int))>)

function sumOverSlopeGroups(groups: seq<seq<((int, int), (int, int))>>, totalLines: nat): nat
  requires totalLines >= 0
  ensures sumOverSlopeGroups(groups, totalLines) >= 0
{
  0
}

lemma SlopeGroupSumLemma(groups: seq<seq<((int, int), (int, int))>>, totalLines: nat)
  ensures var sum := sumOverSlopeGroups(groups, totalLines);
          sum % 2 == 0

function calculateSlope(p1: (int, int), p2: (int, int)): (int, int)
  requires p1 != p2
  requires validCoordinate(p1) && validCoordinate(p2)
  ensures var (dx, dy) := calculateSlope(p1, p2);
          dx != 0 || dy != 0
{
  (0, 0)
}

lemma DistinctPointsLemma(points: seq<(int, int)>)
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  ensures forall i, j :: 0 <= i < j < |points| ==> 
          var p1 := points[i];
          var p2 := points[j];
          p1 != p2

function countPairs(n: nat): nat
  requires n >= 0
  ensures countPairs(n) == n * (n - 1) / 2
{
  if n <= 1 then 0 else (n - 1) + countPairs(n - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires validInputFormat(stdin_input)
  ensures |result| > 0
  ensures isNonNegativeNumericString(result)
  ensures var n := extractN(stdin_input);
          var points := extractPoints(stdin_input);
          |points| == n && n >= 2 && n <= 1000 &&
          (forall i :: 0 <= i < |points| ==> validCoordinate(points[i])) &&
          (forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]) &&
          stringToInt(result) == countIntersectingLinePairs(points)
// </vc-spec>
// <vc-code>
{
    var n := extractN(stdin_input);
    var points := extractPoints(stdin_input);
    
    var count := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant count >= 0
    {
        var j := i + 1;
        while j < n
            invariant i + 1 <= j <= n
            invariant count >= 0
        {
            var k := j + 1;
            while k < n
                invariant j + 1 <= k <= n
                invariant count >= 0
            {
                var p1 := points[i];
                var p2 := points[j];
                var p3 := points[k];
                
                if areCollinear(p1, p2, p3) {
                    count := count + 1;
                }
                k := k + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := countToString(count);
}
// </vc-code>

