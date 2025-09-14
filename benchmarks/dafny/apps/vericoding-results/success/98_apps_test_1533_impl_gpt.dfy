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
  var n := |names|;
  var arr := new string[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall k :: 0 <= k < i ==> arr[k] == (if exists j :: 0 <= j < k && names[j] == names[k] then "YES" else "NO")
    decreases n - i
  {
    if exists j :: 0 <= j < i && names[j] == names[i] {
      arr[i] := "YES";
    } else {
      arr[i] := "NO";
    }
    i := i + 1;
  }
  output := arr[..];
}
// </vc-code>

