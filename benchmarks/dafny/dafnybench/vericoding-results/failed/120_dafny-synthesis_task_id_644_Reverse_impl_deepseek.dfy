

// <vc-helpers>
lemma {:induction false} ReverseLemma(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i <= j < a.Length
  ensures forall k :: (0 <= k < i || j < k < a.Length) ==> a[k] == old(a[k])
  ensures forall k :: i <= k <= j ==> a[k] == old(a[(a.Length-1) - k])
  decreases j - i
{
  if i < j {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    ReverseLemma(a, i+1, j-1);
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  if a.Length > 0 {
    var i := 0;
    var j := a.Length - 1;
    while i < j
      invariant 0 <= i <= j < a.Length
      invariant forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length-1) - k])
      invariant forall k :: j < k < a.Length ==> a[k] == old(a[(a.Length-1) - k])
      invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
      decreases j - i
    {
      var temp := a[i];
      a[i] := a[j];
      a[j] := temp;
      ReverseLemma(a, i+1, j-1);
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>

