// <vc-preamble>
method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i ::
           1 <= i < a.Length
           ==> a[i-1] < a[i]
  requires forall i, j ::
           0 <= i < j < a.Length ==>
           a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i ::
          0 <= i < n ==>
          a[i] < circle
  ensures forall i ::
          n <= i < a.Length ==>
          circle <= a[i]
{
  assume{:axiom} false;
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): removed redundant requires clause */
lemma SearchImpliesExists(a: array<int>, key: int, n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
  requires 0 <= n <= a.Length
  requires forall i :: 0 <= i < n ==> a[i] < key
  requires forall i :: n <= i < a.Length ==> key <= a[i]
  ensures (exists i :: 0 <= i < a.Length && a[i] == key) <==> (n < a.Length && a[n] == key)
{}
// </vc-helpers>

// <vc-spec>
method Tangent(r: array<int>, x: array<int>)
  returns (found: bool)
  requires forall i:: 1 <= i < x.Length ==> 
           x[i-1] < x[i]
  requires forall i, j ::
           0 <= i < j < x.Length ==>
           x[i] < x[j]
  ensures !found ==>
          forall i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length ==>
          r[i] != x[j]
  ensures found ==>
          exists i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length &&
          r[i] == x[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added conditional loop invariants to handle found state */
  found := false;
  var i := 0;
  while i < r.Length && !found
    invariant 0 <= i <= r.Length
    invariant !found ==> (forall k, j :: 0 <= k < i && 0 <= j < x.Length ==> r[k] != x[j])
    invariant found ==> (exists k, j :: 0 <= k < i && 0 <= j < x.Length && r[k] == x[j])
  {
    var n := BinarySearch(x, r[i]);
    SearchImpliesExists(x, r[i], n);

    if n < x.Length && x[n] == r[i] {
      found := true;
    }
    i := i + 1;
  }
}
// </vc-code>
