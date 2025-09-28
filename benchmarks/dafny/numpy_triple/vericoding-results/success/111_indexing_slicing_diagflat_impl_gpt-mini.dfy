// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function IsZero(x: real): bool { x == 0.0 }

lemma ReflReal(a: real)
  ensures a == a
{
  assert a == a;
}

// </vc-helpers>

// <vc-spec>
method DiagFlat(v: seq<real>) returns (result: seq<seq<real>>)
  requires |v| >= 0
  ensures |result| == |v|  // Square matrix: number of rows equals input length
  ensures forall i :: 0 <= i < |result| ==> |result[i]| == |v|  // Each row has correct length
  ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && i == j ==> result[i][j] == v[i]  // Diagonal elements
  ensures forall i, j :: 0 <= i < |v| && 0 <= j < |v| && i != j ==> result[i][j] == 0.0  // Off-diagonal elements are zero
// </vc-spec>
// <vc-code>
{
  var n := |v|;
  var res: seq<seq<real>> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |res| == i
    invariant forall p :: 0 <= p < i ==> |res[p]| == n && (forall q :: 0 <= q < n ==> if p == q then res[p][q] == v[p] else res[p][q] == 0.0)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall q :: 0 <= q < j ==> (if i == q then row[q] == v[i] else row[q] == 0.0)
    {
      var val := if i == j then v[i] else 0.0;
      row := row + [val];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}

// </vc-code>
