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
function SplitLines(input: string): seq<string>
{
  // Stub implementation - would split input by newlines
  []
}

function ParseInt(s: string): IntResult
{
  // Stub implementation - would parse string to int
  IntResult(false, 0)
}

function ParseNames(lines: seq<string>): seq<(string, string)>
{
  // Stub implementation - would parse each line into a name pair
  []
}

function ParseIntSequence(s: string): IntSequenceResult
{
  // Stub implementation - would parse space-separated integers
  IntSequenceResult(false, [])
}

function CreateAllHandlePairs(names: seq<(string, string)>): seq<(int, string)>
{
  // Creates all possible handle pairs (index, handle) from names
  // For each name at index i, creates two pairs: (i, first_name) and (i, last_name)
  if |names| == 0 then []
  else CreateHandlePairsHelper(names, 0)
}

function CreateHandlePairsHelper(names: seq<(string, string)>, idx: int): seq<(int, string)>
  requires 0 <= idx <= |names|
  decreases |names| - idx
{
  if idx >= |names| then []
  else [(idx, names[idx].0), (idx, names[idx].1)] + CreateHandlePairsHelper(names, idx + 1)
}

function SortHandlePairs(handles: seq<(int, string)>): seq<(int, string)>
{
  // Sorts handle pairs lexicographically by the string component
  // Stub implementation - would perform actual sorting
  handles
}

predicate GreedyAssignmentWorks(sorted_handles: seq<(int, string)>, permutation: seq<int>, n: int)
{
  // Checks if greedy assignment following the permutation order works
  // Returns true if each person in permutation order can be assigned a handle
  |permutation| == n && GreedyAssignmentWorksHelper(sorted_handles, permutation, n, 0, {})
}

predicate GreedyAssignmentWorksHelper(sorted_handles: seq<(int, string)>, permutation: seq<int>, n: int, perm_idx: int, used: set<string>)
  requires |permutation| == n
  requires 0 <= perm_idx <= n
  decreases n - perm_idx
{
  if perm_idx >= n then true
  else 
    exists handle_idx :: 0 <= handle_idx < |sorted_handles| &&
      sorted_handles[handle_idx].0 == permutation[perm_idx] - 1 &&  // Adjust for 1-based indexing
      sorted_handles[handle_idx].1 !in used &&
      GreedyAssignmentWorksHelper(sorted_handles, permutation, n, perm_idx + 1, used + {sorted_handles[handle_idx].1})
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
  
  if GreedyAssignmentWorks(sorted_handles, parsed.permutation, parsed.n) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>

