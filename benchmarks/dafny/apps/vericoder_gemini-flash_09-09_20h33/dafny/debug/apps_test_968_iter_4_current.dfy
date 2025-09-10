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
function SplitLines(s: string): seq<string>
  ensures forall i :: 0 <= i < |SplitLines(s)| ==> |SplitLines(s)[i]| > 0 || i == |SplitLines(s)| - 1
  ensures forall i :: 0 <= i < |SplitLines(s)| - 1 ==> SplitLines(s)[i] != ""
{
  if s == "" then []
  else
    var newline_index := -1;
    for i := 0 to |s| - 1
      invariant 0 <= i <= |s|
      invariant newline_index == -1 || (0 <= newline_index < i && s[newline_index] == '\n')
    {
      if s[i] == '\n' then
        newline_index := i;
        break;
      }
    if newline_index == -1 then
      [s]
    else
      [s[..newline_index]] + SplitLines(s[newline_index+1..])
}

function ParseInt(s: string): IntResult
{
  var value := 0;
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant value >= 0
    invariant forall k :: 0 <= k < i ==> '0' <= s[k] <= '9'
  {
    if '0' <= s[i] <= '9' then
      value := value * 10 + (s[i] as int - '0' as int);
    else
      return IntResult(false, 0);
  }
  return IntResult(true, value);
}

function ParseNames(lines: seq<string>): seq<(string, string)>
  ensures |ParseNames(lines)| == |lines|
{
  var names := new seq<(string, string)>(|lines|, (x: int) => ("", ""));
  for i := 0 to |lines|-1
    invariant 0 <= i <= |lines|
    invariant forall j :: 0 <= j < i ==> !(names[j].0 == "" && names[j].1 == "")
  {
    var parts := SplitLineToTwo(lines[i], ' ');
    if |parts| == 2 then
      names := names[i := (parts[0], parts[1])];
    else
      return new seq<(string, string)>(|lines|, (x: int) => ("", "")); // Indicate error
  }
  return names;
}

function SplitLineToTwo(s: string, separator: char): seq<string>
{
  var sep_index := -1;
  for i := 0 to |s|-1
    invariant 0 <= i <= |s|
    invariant sep_index == -1 || (0 <= sep_index < i && s[sep_index] == separator)
  {
    if s[i] == separator then
      sep_index := i;
      break;
    }
  if sep_index == -1 then
    [s]
  else
    [s[..sep_index], s[sep_index+1..]]
}

function ParseIntSequence(s: string): IntSequenceResult
{
  var parts := SplitLineToTwo(s, ' '); // Assuming space separated integers
  if |parts| == 0 then
    return IntSequenceResult(false, []);
  var sequence := new seq<int>(|parts|, i => 0);
  for i := 0 to |parts|-1
    invariant 0 <= i <= |parts|
    invariant forall j :: 0 <= j < i ==> (ParseInt(parts[j])).Valid
  {
    var int_res := ParseInt(parts[i]);
    if !int_res.Valid then
      return IntSequenceResult(false, []);
    sequence := sequence[i := int_res.Value];
  }
  return IntSequenceResult(true, sequence);
}

predicate AllElementsUnique(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate IsPermutation(p: seq<int>, n: int)
{
  |p| == n && (forall i :: 0 <= i < n ==> 1 <= p[i] <= n) && AllElementsUnique(p)
}

function CreateAllHandlePairs(names: seq<(string, string)>): seq<(string, string)>
  requires forall i :: 0 <= i < |names| ==> |names[i].0| > 0 && |names[i].1| > 0
  ensures |CreateAllHandlePairs(names)| == |names| * |names| * 4
{
  var handles := new seq<(string, string)>(|names| * |names| * 4, (x: int) => ("", ""));
  var k := 0;
  for i := 0 to |names|-1
    invariant 0 <= i <= |names|
    invariant 0 <= k <= i * |names| * 4
    invariant forall idx :: 0 <= idx < k ==> handles[idx].0 != "" || handles[idx].1 != ""
  {
    var first_name := names[i].0;
    var last_name := names[i].1;
    for j := 0 to |names|-1
      invariant 0 <= j <= |names|
      invariant (i * |names| * 4) <= k <= (i * |names| * 4) + j * 4
      invariant forall idx :: (i * |names| * 4) <= idx < k ==> handles[idx].0 != "" || handles[idx].1 != ""
    {
      handles := handles[k := (first_name, names[j].0)];
      k := k + 1;
      handles := handles[k := (first_name, names[j].1)];
      k := k + 1;
      handles := handles[k := (last_name, names[j].0)];
      k := k + 1;
      handles := handles[k := (last_name, names[j].1)];
      k := k + 1;
    }
  }
  return handles;
}

function SortHandlePairs(handles: seq<(string, string)>): seq<(string, string)>
  ensures |SortHandlePairs(handles)| == |handles|
{
  var arr := handles;
  if |arr| <= 1 then return arr;

  for i := 1 to |arr|-1
    invariant 0 <= i < |arr|
    invariant forall x, y :: 0 <= x < y < i ==> LexLessOrEqual(arr[x].0, arr[y].0) || (arr[x].0 == arr[y].0 && LexLessOrEqual(arr[x].1, arr[y].1))
    invariant IsPermutationOfOriginal(handles, arr)
  {
    var j := i;
    while j > 0 &&
          (LexLess(arr[j].0, arr[j-1].0) ||
           (arr[j].0 == arr[j-1].0 && LexLess(arr[j].1, arr[j-1].1)))
      invariant 0 < j <= i
      invariant forall x, y :: 0 <= x < y < j ==> LexLessOrEqual(arr[x].0, arr[y].0) || (arr[x].0 == arr[y].0 && LexLessOrEqual(arr[x].1, arr[y].1))
      invariant forall x, y :: j <= x < y < i+1 ==> LexLessOrEqual(arr[x].0, arr[y].0) || (arr[x].0 == arr[y].0 && LexLessOrEqual(arr[x].1, arr[y].1))
      invariant IsPermutationOfOriginal(handles, arr)
    {
      var temp := arr[j];
      arr := arr[j := arr[j-1]];
      arr := arr[j-1 := temp];
      j := j - 1;
    }
  }
  return arr;
}
predicate IsPermutationOfOriginal<T>(original: seq<T>, current: seq<T>)
{
  |original| == |current| &&
  multiset(original) == multiset(current)
}

predicate GreedyAssignmentWorks(sorted_handles: seq<(string, string)>, permutation: seq<int>, n: int)
  requires |sorted_handles| == n * n * 4
  requires IsPermutation(permutation, n)
{
  var current_assigned_persons := new set<int>();
  var current_assigned_handles := new set<string>();

  for k := 0 to n-1
    invariant 0 <= k <= n
    invariant current_assigned_persons <= set p | 1 <= p <= n
    invariant forall h :: h in current_assigned_handles ==> h != ""
  {
    var person_id := permutation[k]; // This is 1-indexed

    var found_assignment_for_this_person := false;
    for l := 0 to |sorted_handles|-1
      invariant 0 <= l <= |sorted_handles|
      invariant !found_assignment_for_this_person ==> (forall h_idx :: 0 <= h_idx < l ==> sorted_handles[h_idx].0 in current_assigned_handles || sorted_handles[h_idx].1 in current_assigned_handles )
    {
      var h0 := sorted_handles[l].0;
      var h1 := sorted_handles[l].1;

      if h0 != "" && h1 != "" && !(h0 in current_assigned_handles) && !(h1 in current_assigned_handles) then
        current_assigned_persons := current_assigned_persons + {person_id};
        current_assigned_handles := current_assigned_handles + {h0, h1};
        found_assignment_for_this_person := true;
        break; // Found a handle for this person, move to the next person in permutation
    }
    if !found_assignment_for_this_person then return false; // Failed to assign a handle for `person_id`
  }
  return |current_assigned_persons| == n; // All persons were successfully assigned
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
  if GreedyAssignmentWorks(sorted_handles, parsed.permutation, parsed.n) then
    result := "YES";
  else
    result := "NO";
}
// </vc-code>

