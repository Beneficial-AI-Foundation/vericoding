// <vc-preamble>
predicate ValidInput(n: int, points: seq<(int, int)>, w: seq<int>)
{
  1 <= n <= 100000 &&
  |points| == n &&
  |w| == n &&
  AllPointsInBounds(points) &&
  AllWValuesInBounds(w) &&
  AllPointsDistinct(points) &&
  IsStaircaseSet(points)
}

predicate AllPointsInBounds(points: seq<(int, int)>)
{
  forall p :: p in points ==> 0 <= p.0 <= 100000 && 0 <= p.1 <= 100000
}

predicate AllWValuesInBounds(w: seq<int>)
{
  forall wi :: wi in w ==> -100000 <= wi <= 100000
}

predicate AllPointsDistinct(points: seq<(int, int)>)
{
  forall i, j :: 0 <= i < j < |points| ==> points[i] != points[j]
}

predicate IsStaircaseSet(points: seq<(int, int)>)
{
  forall p :: p in points ==>
    forall x', y' :: 0 <= x' <= p.0 && 0 <= y' <= p.1 ==> (x', y') in points
}

predicate ValidAssignment(assignment: seq<(int, int)>, points: seq<(int, int)>, w: seq<int>)
{
  |assignment| == |points| == |w| &&
  AssignmentCoversAllPoints(assignment, points) &&
  AssignmentFollowsAestheticConstraint(assignment) &&
  AssignmentSatisfiesSpecialValues(assignment, w)
}

predicate AssignmentCoversAllPoints(assignment: seq<(int, int)>, points: seq<(int, int)>)
{
  |assignment| == |points| &&
  (forall p :: p in assignment ==> p in points) &&
  (forall p :: p in points ==> p in assignment) &&
  (forall i, j :: 0 <= i < j < |assignment| ==> assignment[i] != assignment[j])
}

predicate AssignmentFollowsAestheticConstraint(assignment: seq<(int, int)>)
{
  forall i, j :: 0 <= i < j < |assignment| ==> 
    assignment[j].0 >= assignment[i].0 && assignment[j].1 >= assignment[i].1
}

predicate AssignmentSatisfiesSpecialValues(assignment: seq<(int, int)>, w: seq<int>)
{
  |assignment| == |w| &&
  forall i :: 0 <= i < |assignment| ==> assignment[i].1 - assignment[i].0 == w[i]
}

predicate AssignmentExists(points: seq<(int, int)>, w: seq<int>)
{
  var pointSpecialValues := set p | p in points :: p.1 - p.0;
  var requiredSpecialValues := set wi | wi in w :: wi;
  pointSpecialValues == requiredSpecialValues
}
// </vc-preamble>

// <vc-helpers>
method ParseInt(s: string) returns (result: int)
  requires |s| >= 0
{
  result := 0;
  var sign := 1;
  var start := 0;

  if |s| > 0 && s[0] == '-' {
    sign := -1;
    start := 1;
  }

  for i := start to |s|
    invariant result >= 0
  {
    if i < |s| && '0' <= s[i] <= '9' {
      var digit := s[i] as int - '0' as int;
      result := result * 10 + digit;
    }
  }

  result := result * sign;
}

method Split(s: string, delimiter: string) returns (parts: array<string>)
  requires |s| >= 0
  requires |delimiter| > 0
  ensures parts.Length >= 1
{
  parts := new string[2];
  var delimIndex := -1;

  if |s| >= |delimiter| {
    for i := 0 to |s| - |delimiter| + 1
      invariant 0 <= i <= |s| - |delimiter| + 1
      invariant delimIndex >= -1
    {
      if i + |delimiter| <= |s| && s[i..i+|delimiter|] == delimiter {
        delimIndex := i;
        break;
      }
    }
  }

  if delimIndex != -1 {
    parts[0] := s[0..delimIndex];
    parts[1] := s[delimIndex + |delimiter|..];
  } else {
    parts[0] := s;
    parts[1] := "";
  }
}

method StringToPoint(s: string) returns (result: (int, int))
  requires |s| >= 0
{
  var parts := Split(s, " ");
  var x := 0;
  var y := 0;

  if parts.Length >= 1 {
    x := ParseInt(parts[0]);
  }
  if parts.Length >= 2 {
    y := ParseInt(parts[1]);
  }

  result := (x, y);
}
// </vc-helpers>

// <vc-spec>
method Solve(n: int, points: seq<(int, int)>, w: seq<int>) returns (success: bool, assignment: seq<(int, int)>)
  requires ValidInput(n, points, w)
  ensures success <==> AssignmentExists(points, w)
  ensures success ==> ValidAssignment(assignment, points, w)
  ensures !success ==> assignment == []
// </vc-spec>
// <vc-code>
{
  if !AssignmentExists(points, w) {
    success := false;
    assignment := [];
    return;
  }

  var result := [];
  var used := new bool[n];
  
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> !used[j]
  {
    used[i] := false;
  }

  for pos := 0 to n
    invariant 0 <= pos <= n
    invariant |result| == pos
    invariant forall i :: 0 <= i < pos ==> result[i] in points
    invariant forall i :: 0 <= i < pos ==> result[i].1 - result[i].0 == w[i]
    invariant forall i, j :: 0 <= i < j < pos ==> result[i] != result[j]
    invariant forall i :: 0 <= i < pos ==> (exists k :: 0 <= k < n && points[k] == result[i] && used[k])
    invariant forall k :: 0 <= k < n ==> used[k] == (exists i :: 0 <= i < pos && result[i] == points[k])
    invariant pos > 0 ==> AssignmentFollowsAestheticConstraint(result)
  {
    var found := false;
    var selectedPoint := (0, 0);
    var selectedIndex := 0;
    
    for pointIdx := 0 to n
      invariant 0 <= pointIdx <= n
      invariant found ==> (0 <= selectedIndex < n && !used[selectedIndex])
      invariant found ==> points[selectedIndex] == selectedPoint
      invariant found ==> selectedPoint.1 - selectedPoint.0 == w[pos]
      invariant found ==> selectedPoint in points
    {
      if !used[pointIdx] && points[pointIdx].1 - points[pointIdx].0 == w[pos] {
        var canPlace := true;
        
        if pos > 0 {
          var lastPoint := result[pos - 1];
          if points[pointIdx].0 < lastPoint.0 || points[pointIdx].1 < lastPoint.1 {
            canPlace := false;
          }
        }
        
        if canPlace {
          selectedPoint := points[pointIdx];
          selectedIndex := pointIdx;
          found := true;
          break;
        }
      }
    }
    
    if !found {
      success := false;
      assignment := [];
      return;
    }
    
    used[selectedIndex] := true;
    result := result + [selectedPoint];
  }

  success := true;
  assignment := result;
}
// </vc-code>
