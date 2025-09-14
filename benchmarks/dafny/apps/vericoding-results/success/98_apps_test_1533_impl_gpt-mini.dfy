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
    invariant forall k :: 0 <= k < i ==> names[k] in seen
    invariant forall s :: s in seen ==> exists k :: 0 <= k < i && names[k] == s
    invariant forall k :: 0 <= k < i ==> output[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
    decreases |names| - i
  {
    var n := names[i];
    var seenBefore := n in seen;
    if seenBefore {
      output := output + ["YES"];
    } else {
      output := output + ["NO"];
      seen := seen + {n};
    }
    i := i + 1;
  }
  return output;
}
// </vc-code>

