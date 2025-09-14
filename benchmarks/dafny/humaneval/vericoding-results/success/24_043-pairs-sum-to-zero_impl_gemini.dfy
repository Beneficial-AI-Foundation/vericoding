// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l : seq<int>) returns (result : bool)

    ensures result ==> exists i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j && l[i] + l[j] == 0
    ensures !result ==> forall i : int, j : int :: 0 <= i < |l| && 0 <= j < |l| && i != j ==> l[i] + l[j] != 0
// </vc-spec>
// <vc-code>
{
  result := false;
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant result ==> (exists k, m :: 0 <= k < i && k < m < |l| && l[k] + l[m] == 0)
    invariant !result ==> (forall k, m :: 0 <= k < i && k < m < |l| ==> l[k] + l[m] != 0)
  {
    var j := i + 1;
    while j < |l|
      invariant 0 <= i < |l|
      invariant i + 1 <= j <= |l|
      invariant !result ==> (forall m :: i < m < j ==> l[i] + l[m] != 0)
      invariant !result ==> (forall k, m :: 0 <= k < i && k < m < |l| ==> l[k] + l[m] != 0)
    {
      if l[i] + l[j] == 0 {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
