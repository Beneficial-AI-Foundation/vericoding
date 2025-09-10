predicate ValidOutput(names: seq<string>, output: seq<string>)
{
    |output| == |names| &&
    forall i :: 0 <= i < |names| ==> 
        output[i] == (if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO")
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(names: seq<string>) returns (output: seq<string>)
    ensures ValidOutput(names, output)
// </vc-spec>
// <vc-code>
{
  output := [];
  var seen: set<string> := {};
  var i := 0;
  while i < |names| 
    invariant 0 <= i <= |names|
    invariant |output| == i
    invariant forall k :: 0 <= k < i ==> 
      (output[k] == "YES") == (exists j :: 0 <= j < k && names[j] == names[k])
    invariant seen == set j | 0 <= j < i :: names[j]
  {
    if names[i] in seen {
      output := output + ["YES"];
    } else {
      output := output + ["NO"];
    }
    seen := seen + {names[i]};
    i := i + 1;
  }
}
// </vc-code>

