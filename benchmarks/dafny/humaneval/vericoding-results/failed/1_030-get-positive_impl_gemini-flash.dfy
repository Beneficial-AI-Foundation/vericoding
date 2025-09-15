// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unused helper function */
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)

    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed postcondition and loop invariant issues */
{
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall j : int :: 0 <= j < |result| ==> result[j] > 0
    invariant forall j1 : int :: 0 <= j1 < |result| ==> (exists j2 : int :: 0 <= j2 < i && result[j1] == l[j2])
    invariant forall j1 : int :: 0 <= j1 < i && l[j1] > 0 ==> (exists j2 : int :: 0 <= j2 < |result| && l[j1] == result[j2])
    invariant |result| <= i
    invariant forall j1 : int :: 0 <= j1 < |result| ==> (exists j2 : int :: 0 <= j2 < |l| && l[j2] == result[j1])
  {
    if l[i] > 0 {
      result := result + [l[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
