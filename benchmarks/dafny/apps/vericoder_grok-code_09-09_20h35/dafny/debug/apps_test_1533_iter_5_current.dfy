predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
  output := [];
  var idx := 0;
  while idx < |names|
    invariant 0 <= idx <= |names|
    invariant |output| == idx
    invariant forall k :: 0 <= k < idx ==> 
      output[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
  {
    var found := false;
    var j := 0;
    while j < idx
      invariant 0 <= j <= idx
      decreases idx - j
    {
      if names[j] == names[idx] {
        found := true;
      }
      j := j + 1;
    }
    if found {
      output := output + ["YES"];
    } else {
      output := output + ["NO"];
    }
    idx := idx + 1;
  }
}
// </vc-code>

