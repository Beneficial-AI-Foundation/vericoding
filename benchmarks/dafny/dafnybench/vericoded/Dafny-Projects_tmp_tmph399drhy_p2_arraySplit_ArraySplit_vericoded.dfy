// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ArraySplit (a : array<int>) returns (b : array<int>, c : array<int>)
  ensures fresh(b)
  ensures fresh(c)
  ensures a[..] == b[..] + c[..]
  ensures a.Length == b.Length + c.Length
  ensures a.Length > 1 ==> a.Length > b.Length
  ensures a.Length > 1 ==> a.Length > c.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): implemented with while loops to fix index out of range errors */
  var mid := a.Length / 2;
  b := new int[mid];
  c := new int[a.Length - mid];

  var i := 0;
  while i < mid
    invariant 0 <= i <= mid
    invariant forall k :: 0 <= k < i ==> b[k] == a[k]
  {
    b[i] := a[i];
    i := i + 1;
  }

  var j := 0;
  while j < c.Length
    invariant 0 <= j <= c.Length
    invariant forall k :: 0 <= k < b.Length ==> b[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[k] == a[mid + k]
  {
    c[j] := a[mid + j];
    j := j + 1;
  }
}
// </vc-code>
