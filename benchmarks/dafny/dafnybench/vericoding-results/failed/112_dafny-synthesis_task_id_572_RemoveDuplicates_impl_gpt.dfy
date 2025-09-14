

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method RemoveDuplicates(a: array<int>) returns (result: seq<int>)
    requires a != null
    ensures forall x :: x in result <==> exists i :: 0 <= i < a.Length && a[i] == x
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  var r: seq<int> := [];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in r <==> exists j :: 0 <= j < i && a[j] == x
    invariant forall p, q :: 0 <= p < q < |r| ==> r[p] != r[q]
    decreases a.Length - i
  {
    var v := a[i];
    if !(v in r) {
      r := r + [v];
    }
    i := i + 1;
  }
  result := r;
}
// </vc-code>

