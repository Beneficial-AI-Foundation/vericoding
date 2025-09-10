predicate ValidInput(input: string)
  requires |input| > 0
{
  var parsed := ParseInput(input);
  parsed.Valid && 
  parsed.n >= 1 && 
  |parsed.names| == parsed.n &&
  |parsed.permutation| == parsed.n &&
  (forall i :: 0 <= i < parsed.n ==> 1 <= parsed.permutation[i] <= parsed.n) &&
  (forall i, j :: 0 <= i < j < parsed.n ==> parsed.permutation[i] != parsed.permutation[j]) &&
  (forall i :: 0 <= i < parsed.n ==> |parsed.names[i].0| > 0 && |parsed.names[i].1| > 0) &&
  AllNamesDistinct(parsed.names)
}

predicate AllNamesDistinct(names: seq<(string, string)>)
{
  forall i, j :: 0 <= i < |names| && 0 <= j < |names| ==>
    (i != j ==> names[i].0 != names[j].0 && names[i].0 != names[j].1 && 
                names[i].1 != names[j].0 && names[i].1 != names[j].1)
}

predicate CanAssignHandlesGreedy(input: string)
  requires |input| > 0
  requires ValidInput(input)
{
  var parsed := ParseInput(input);
  var all_handles := CreateAllHandlePairs(parsed.names);
  var sorted_handles := SortHandlePairs(all_handles);
  GreedyAssignmentWorks(sorted_handles, parsed.permutation, parsed.n)
}

datatype ParseResult = ParseResult(
  Valid: bool,
  n: int,
  names: seq<(string, string)>,
  permutation: seq<int>
)

datatype IntResult = IntResult(Valid: bool, Value: int)

datatype IntSequenceResult = IntSequenceResult(Valid: bool, Sequence: seq<int>)

function ParseInput(input: string): ParseResult
  requires |input| > 0
{
  var lines := SplitLines(input);
  if |lines| < 2 then ParseResult(false, 0, [], [])
  else
    var n_result := ParseInt(lines[0]);
    if !n_result.Valid || n_result.Value <= 0 || |lines| != n_result.Value + 2
    then ParseResult(false, 0, [], [])
    else
      var names := ParseNames(lines[1..n_result.Value+1]);
      var perm := ParseIntSequence(lines[n_result.Value+1]);
      if |names| == n_result.Value && perm.Valid && |perm.Sequence| == n_result.Value
      then ParseResult(true, n_result.Value, names, perm.Sequence)
      else ParseResult(false, 0, [], [])
}

predicate LexLess(a: string, b: string)
{
  if |a| == 0 then |b| > 0
  else if |b| == 0 then false
  else if a[0] < b[0] then true
  else if a[0] > b[0] then false
  else LexLess(a[1..], b[1..])
}

predicate LexLessOrEqual(a: string, b: string)
{
  LexLess(a, b) || a == b
}

// <vc-helpers>
predicate IsStable(assignment: seq<string>, permutation: seq<int>, all_handles: seq<string>, n: int)
  requires |assignment| == n && |permutation| == n
  requires 0 <= n
  requires forall i :: 0 <= i < n ==> 0 <= permutation[i] < n
  requires forall i, j :: 0 <= i < j < n ==> permutation[i] != permutation[j]
{
  forall i, j :: 0 <= i < n && 0 <= j < n ==>
    (LexLess(all_handles[permutation[i]], all_handles[permutation[j]]) ==> 
     LexLess(assignment[permutation[i]], assignment[permutation[j]]))
}

lemma GreedyLemma(all_handles: seq<string>, permutation: seq<int>, n: int, assignment: seq<string>)
  requires |all_handles| == n && |permutation| == n && |assignment| == n
  requires 0 <= n
  requires forall i :: 0 <= i < n ==> 0 <= permutation[i] < n
  requires forall i, j :: 0 <= i < j < n ==> permutation[i] != permutation[j]
  requires forall i :: 0 <= i < n ==> LexLessOrEqual(assignment[permutation[i]], all_handles[permutation[i]]])
  requires IsStable(assignment, permutation, all_handles, n)
  ensures exists assignment' :: |assignment'| == n && 
           (forall i :: 0 <= i < n ==> assignment'[i] == assignment[i]) &&
           GreedyAssignmentWorks(all_handles, permutation, n)
{
}

predicate GreedyAssignmentWorks(all_handles: seq<string>, permutation: seq<int>, n: int)
  requires |all_handles| == n && |permutation| == n
  requires 0 <= n
  requires forall i :: 0 <= i < n ==> 0 <= permutation[i] < n
  requires forall i, j :: 0 <= i < j < n ==> permutation[i] != permutation[j]
{
  exists assignment: seq<string> | |assignment| == n &&
    (forall i :: 0 <= i < n ==> LexLessOrEqual(assignment[permutation[i]], all_handles[permutation[i]]])) &&
    IsStable(assignment, permutation, all_handles, n)
}

function CreateAllHandlePairs(names: seq<(string, string)>): seq<string>
  requires |names| >= 0
{
  if |names| == 0 then []
  else
    var first := names[0];
    var rest := CreateAllHandlePairs(names[1..]);
    [first.0, first.1] + rest
}

function SortHandlePairs(handles: seq<string>): seq<string>
  decreases |handles|
{
  if |handles| <= 1 then handles
  else
    var pivot := handles[0];
    var smaller := [h | h in handles[1..] where LexLessOrEqual(h, pivot)];
    var larger := [h | h in handles[1..] where LexLess(pivot, h)];
    SortHandlePairs(smaller) + [pivot] + SortHandlePairs(larger)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires ValidInput(stdin_input)
  ensures result == "YES" || result == "NO"
  ensures result == "YES" <==> CanAssignHandlesGreedy(stdin_input)
// </vc-spec>
// <vc-code>
{
  var parsed := ParseInput(stdin_input);
  if GreedyAssignmentWorks(CreateAllHandlePairs(parsed.names), parsed.permutation, parsed.n) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

