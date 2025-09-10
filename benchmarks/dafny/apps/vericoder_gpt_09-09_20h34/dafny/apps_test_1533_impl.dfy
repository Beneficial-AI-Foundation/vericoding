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
  var out: seq<string> := [];
  var i := 0;
  while i < |names|
    invariant 0 <= i <= |names|
    invariant |out| == i
    invariant forall k :: 0 <= k < i ==>
      out[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
  {
    var val := if exists j :: 0 <= j < i && names[j] == names[i] then "YES" else "NO";
    out := out + [val];
    i := i + 1;
  }
  output := out;
}
// </vc-code>

