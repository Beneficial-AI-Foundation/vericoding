predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}

// <vc-helpers>
ghost predicate InResult(result: seq<int>, x: int) {
  exists i :: 0 <= i < |result| && result[i] == x
}

function InArrayFunc(a: array<int>, x: int): bool
  reads a
{
  exists i :: 0 <= i < a.Length && a[i] == x
}

function InSeq(s: seq<int>, x: int): bool
{
  exists i :: 0 <= i < |s| && s[i] == x
}
// </vc-helpers>

// <vc-spec>
method SharedElements(a: array<int>, b: array<int>) returns (result: seq<int>)
    // All elements in the output are in both a and b
    ensures forall x :: x in result ==> (InArray(a, x) && InArray(b, x))
    // The elements in the output are all different
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var output: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in output ==> InArray(a, x) && InArray(b, x)
    invariant forall i, j :: 0 <= i < j < |output| ==> output[i] != output[j]
  {
    var x := a[i];
    if InArrayFunc(b, x) && !InSeq(output, x) {
      output := output + [x];
    }
    i := i + 1;
  }
  result := output;
}
// </vc-code>

