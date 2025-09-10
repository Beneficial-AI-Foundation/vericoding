predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
function findFirstOccurrence(names: seq<string>, target: string, limit: int): (index: int)
  requires 0 <= limit <= |names|
  ensures (0 <= index < limit && names[index] == target) || (index == limit && forall k :: 0 <= k < limit ==> names[k] != target)
{
  var i := 0;
  while i < limit
    invariant 0 <= i <= limit
    invariant forall k :: 0 <= k < i ==> names[k] != target
  {
    if names[i] == target then
      return i;
    i := i + 1;
  }
  return limit;
}
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
  var n := |names|;
  var output_arr := new string[n];

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> 
      output_arr[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
  {
    var found_previous := false;
    var j := findFirstOccurrence(names, names[i], i);
    if j < i && names[j] == names[i] then // Verify that a previous occurrence was indeed found
      found_previous := true;
    
    if found_previous then
      output_arr[i] := "YES";
    else
      output_arr[i] := "NO";
  }

  output := output_arr[..];
}
// </vc-code>

