

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j :: 0 <= j < |result| ==> result[j] > 0
    invariant |result| <= i
    invariant forall j :: 0 <= j < i ==> (l[j] > 0 ==> exists k :: 0 <= k < |result| && result[k] == l[j])
    invariant forall j :: 0 <= j < |result| ==> exists k :: 0 <= k < |l| && l[k] == result[j] && l[k] > 0
  {
    if l[i] > 0 {
      result := result + [l[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

