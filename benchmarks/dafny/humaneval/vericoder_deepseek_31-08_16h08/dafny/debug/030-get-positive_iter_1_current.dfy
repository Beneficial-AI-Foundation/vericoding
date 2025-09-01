

// <vc-helpers>
predicate is_positive(x: int) { x > 0 }

lemma filter_preserves_positive_elements(l: seq<int>, result: seq<int>)
  requires forall i :: 0 <= i < |result| ==> result[i] > 0
  requires forall i :: 0 <= i < |l| && l[i] > 0 ==> exists j :: 0 <= j < |result| && result[j] == l[i]
  ensures forall i :: 0 <= i < |l| && l[i] > 0 ==> exists j :: 0 <= j < |result| && result[j] == l[i]
{
}

lemma result_elements_from_original(l: seq<int>, result: seq<int>)
  requires forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < |l| && l[j] == result[i]
  ensures forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < |l| && l[j] == result[i]
{
}
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
  var index := 0;
  
  while index < |l|
    invariant index >= 0
    invariant |result| <= index
    invariant forall i :: i >= 0 && i < |result| ==> result[i] > 0
    invariant forall i :: i >= 0 && i < index && l[i] > 0 ==> exists j :: j >= 0 && j < |result| && result[j] == l[i]
    invariant forall i :: i >= 0 && i < |result| ==> exists j :: j >= 0 && j < index && l[j] == result[i]
  {
    if l[index] > 0 {
      result := result + [l[index]];
    }
    index := index + 1;
  }
}
// </vc-code>

