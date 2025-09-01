

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

lemma seq_length_concat(a: seq<int>, b: seq<int>)
  ensures |a + b| == |a| + |b|
{
}

lemma element_in_concatenation(a: seq<int>, b: seq<int>, x: int)
  ensures (x in a + b) == (x in a || x in b)
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
    invariant 0 <= index <= |l|
    invariant 0 <= |result| <= index
    invariant forall i :: 0 <= i < |result| ==> result[i] > 0
    invariant forall i :: 0 <= i < index && l[i] > 0 ==> exists j :: 0 <= j < |result| && result[j] == l[i]
    invariant forall i :: 0 <= i < |result| ==> exists j :: 0 <= j < index && l[j] == result[i] && l[j] > 0
  {
    if l[index] > 0 {
      var prev_len := |result|;
      result := result + [l[index]];
      assert |result| == prev_len + 1;
      assert result[prev_len] == l[index] && result[prev_len] > 0;
    }
    index := index + 1;
  }
  
  filter_preserves_positive_elements(l, result);
  result_elements_from_original(l, result);
}
// </vc-code>

