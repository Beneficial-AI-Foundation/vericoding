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
datatype Handle = Handle(len: int, str: string)

function CreateAllHandlePairs(names: seq<(string, string)>): seq<Handle>
{
  if |names| == 0 then []
  else
    var f := names[0].0;
    var l := names[0].1;
    var h1 := if |f| > 0 && |l| > 0 then [Handle(|f| + |l|, f + l)] else [];
    var h2 := if !f.IsEmpty() && !l.IsEmpty() then [Handle(1 + |l|, f[..1] + l)] else [];
    var rest := CreateAllHandlePairs(names[1..]);
    h1 + h2 + rest
}

function SortHandlePairs(handles: seq<Handle>): seq<Handle>
  requires forall i :: 0 <= i < |handles| ==> handles[i].len == |handles[i].str|
  decreases |handles|
{
  if |handles| <= 1 then handles
  else
    var pivot := handles[|handles|/2];
    var left := [];
    var right := [];
    var eq := [];
    for i := 0 to |handles|-1
      invariant |left| + |right| + |eq| + (|handles| - 1 - i) == |handles|-1
    {
      if handles[i].len < pivot.len ||
         (handles[i].len == pivot.len && LexLess(handles[i].str, pivot.str)) {
        left := left + [handles[i]];
      } else if handles[i].len > pivot.len ||
                 (handles[i].len == pivot.len && LexLess(pivot.str, handles[i].str)) {
        right := right + [handles[i]];
      } else {
        eq := eq + [handles[i]];
      }
    }
    SortHandlePairs(left) + eq + SortHandlePairs(right)
}

predicate GreedyAssignmentWorks(sorted_handles: seq<Handle>, permutation: seq<int>, n: int)
  requires forall i :: 0 <= i < |sorted_handles| ==> sorted_handles[i].len == |sorted_handles[i].str|
  requires |permutation| == n
  requires forall i :: 0 <= i < n ==> 0 <= permutation[i]-1 < n
{
  var assigned := multiset(s : string | false); // start empty
  GreedyAssign(sorted_handles, permutation, n, 0, assigned)
}

predicate GreedyAssign(handles: seq<Handle>, perm: seq<int>, n: int, idx: int, assigned: multiset<string>)
  requires 0 <= idx <= n
  requires forall i :: 0 <= i < |handles| ==> handles[i].len == |handles[i].str|
  requires |perm| == n
  requires forall i :: 0 <= i < n ==> 0 <= perm[i]-1 < n
  decreases n - idx
{
  if idx == n then true
  else
    // Find the first handle that is not in assigned
    var h := FindAvailableHandle(handles, assigned);
    h.None? || GreedyAssign(handles, perm, n, idx+1, assigned + multiset{h.v.str})
}

datatype MaybeHandle = None | Some(v: Handle)

function FindAvailableHandle(handles: seq<Handle>, assigned: multiset<string>): MaybeHandle
  requires forall i :: 0 <= i < |handles| ==> handles[i].len == |handles[i].str|
{
  if |handles| == 0 then None
  else
    var h := handles[0];
    if h.str !in assigned then Some(h)
    else FindAvailableHandle(handles[1..], assigned)
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
  var all_handles := CreateAllHandlePairs(parsed.names);
  var sorted_handles := SortHandlePairs(all_handles);
  var assigned := multiset(s : string | false);
  if GreedyAssign(sorted_handles, parsed.permutation, parsed.n, 0, assigned) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

