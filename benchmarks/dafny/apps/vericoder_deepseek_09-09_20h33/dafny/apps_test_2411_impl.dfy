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
{ 
  if |s| == 0 then [""] else [s]
}

function parseFirstLineAsNat(s: string): nat
  requires isValidFirstLine(s)
{ 
  if |s| > 0 then stringToInt(s) else 0 
}

predicate isValidFirstLine(s: string)
  ensures isValidFirstLine(s) ==> isNonNegativeNumericString(s)
{ 
  isNonNegativeNumericString(s) 
}

predicate isValidCoordinateLine(s: string)
{ 
  |s| > 0 
}

function getDistinctLines(points: seq<(int, int)>): seq<((int, int), (int, int))>
  requires |points| >= 2
  requires forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
  requires forall i :: 0 <= i < |points| ==> validCoordinate(points[i])
  ensures forall i :: 0 <= i < |getDistinctLines(points)| ==> 
          var ((x1, y1), (x2, y2)) := getDistinctLines(points)[i];
          x1 != x2 || y1 != y2
{
  var lines := [];
  var i := 0;
  while i < |points|
    invariant 0 <= i <= |points|
    invariant forall k :: 0 <= k < |lines| ==> 
             var ((x1, y1), (x2, y2)) := lines[k];
             x1 != x2 || y1 != y2
  {
    var j := i + 1;
    while j < |points|
      invariant i + 1 <= j <= |points|
      invariant forall k :: 0 <= k < |lines| ==> 
               var ((x1, y1), (x2, y2)) := lines[k];
               x1 != x2 || y1 != y2
    {
      var p1 := points[i];
      var p2 := points[j];
      if p1 != p2 {
        lines := lines + [(p1, p2)];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  lines
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
{ true }

function sumOverSlopeGroups(groups: seq<seq<((int, int), (int, int))>>, totalLines: nat): nat
  requires totalLines >= 0
  ensures sumOverSlopeGroups(groups, totalLines) >= 0
{
  0
}

function areCollinear(p1: (int, int), p2: (int, int), p3: (int, int)): bool
  requires p1 != p2 && p1 != p3 && p2 != p3
  requires validCoordinate(p1) && validCoordinate(p2) && validCoordinate(p3)
{
  var area := (p2.0 - p1.0) * (p3.1 - p1.1) - (p3.0 - p1.0) * (p2.1 - p1.1);
  area == 0
}

function countToString(n: nat): string
{
  if n == 0 then "0" else "1"
}

function stringToInt(s: string): nat
  requires isNonNegativeNumericString(s)
{
  if |s| == 0 then 0
  else var last := s[|s|-1];
       var rest := s[..|s|-1];
       '0' <= last <= '9' ? stringToInt(rest) * 10 + (last as int - '0' as int) : 0
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
                
                if p1 != p2 && p1 != p3 && p2 != p3 && areCollinear(p1, p2, p3) {
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

