// <vc-preamble>
function MultisetCount<T(==)>(s: seq<T>, x: T): nat
{
    |set i | 0 <= i < |s| && s[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): implemented lemma body using multiset theory */
lemma Lemma_SwapMaintainsMultiset<T(==)>(s: seq<T>, i: int, j: int)
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  ensures forall x :: MultisetCount(s[i := s[j]][j := s[i]], x) == MultisetCount(s, x)
{
    var s_swapped := s[i := s[j]][j := s[i]];
    assert multiset(s_swapped) == multiset(s);
}
// </vc-helpers>

// <vc-spec>
method Sort(a: array<int>) returns (result: array<int>)
    ensures
        result.Length == a.Length &&
        (forall i, j :: 0 <= i < j < result.Length ==> result[i] <= result[j]) &&
        (forall x :: MultisetCount(result[..], x) == MultisetCount(a[..], x))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): added asserts to prove multiset preservation */
  result := new int[a.Length];
  if a.Length > 0 {
    forall k | 0 <= k < a.Length {
      result[k] := a[k];
    }
    assert result[..] == a[..];
  }

  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
    invariant forall k, l :: 0 <= k < l < i ==> result[k] <= result[l]
    invariant forall k :: 0 <= k < i ==> forall l :: i <= l < result.Length ==> result[k] <= result[l]
    invariant multiset(result[..]) == multiset(a[..])
  {
    var min_idx := i;
    var k := i + 1;
    while k < result.Length
      invariant i < k <= result.Length
      invariant i <= min_idx < k
      invariant forall j :: i <= j < k ==> result[min_idx] <= result[j]
    {
      if result[k] < result[min_idx] {
        min_idx := k;
      }
      k := k + 1;
    }

    if i < result.Length { // Necessary for termination and valid indexing
      var old_result_at_i := result[i];
      var old_result_at_min_idx := result[min_idx];

      if i != min_idx {
        var temp_seq := result[..];
        result[i], result[min_idx] := result[min_idx], result[i];
        assert result[..] == temp_seq[i := temp_seq[min_idx]][min_idx := temp_seq[i]];
        Lemma_SwapMaintainsMultiset(temp_seq, i, min_idx);
      }
    }
    
    i := i + 1;
  }
}
// </vc-code>
