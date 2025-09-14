

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)
   // post-conditions-start
    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |l|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall p,q :: 0 <= p < i && 0 <= q < n && p != q ==> l[p] + l[q] != 0
    decreases n - i
  {
    var j := i + 1;
    while j < n
      invariant 0 <= j <= n
      invariant forall p,q :: (0 <= p < i && 0 <= q < n && p != q) || (p == i && 0 <= q < j && p != q) ==> l[p] + l[q] != 0
      decreases n - j
    {
      if l[i] + l[j] == 0 {
        assert 0 <= i < n && 0 <= j < n && i != j && l[i] + l[j] == 0;
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}
// </vc-code>

