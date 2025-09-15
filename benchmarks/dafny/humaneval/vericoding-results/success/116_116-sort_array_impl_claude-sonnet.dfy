// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed lemma body to prove multiset preservation */
function CountSetBits(n: nat): nat { popcount(n) }

predicate SortedByPopcount(s: seq<nat>) {
  forall i, j :: 0 <= i < j < |s| ==> popcount(s[i]) <= popcount(s[j])
}

lemma MultisetSplit(arr: seq<nat>, pos: int)
  requires 0 <= pos <= |arr|
  ensures multiset(arr[..pos]) + multiset(arr[pos..]) == multiset(arr)
{
  if pos == 0 {
    assert arr[..0] == [];
    assert arr[0..] == arr;
    assert multiset([]) + multiset(arr) == multiset(arr);
  } else if pos == |arr| {
    assert arr[..|arr|] == arr;
    assert arr[|arr|..] == [];
    assert multiset(arr) + multiset([]) == multiset(arr);
  } else {
    assert arr == arr[..pos] + arr[pos..];
  }
}

method InsertSorted(arr: seq<nat>, elem: nat) returns (result: seq<nat>)
  requires SortedByPopcount(arr)
  ensures |result| == |arr| + 1
  ensures multiset(result) == multiset(arr) + multiset{elem}
  ensures SortedByPopcount(result)
{
  var pos := 0;
  while pos < |arr| && popcount(arr[pos]) <= popcount(elem)
    invariant 0 <= pos <= |arr|
    invariant forall k :: 0 <= k < pos ==> popcount(arr[k]) <= popcount(elem)
  {
    pos := pos + 1;
  }
  
  MultisetSplit(arr, pos);
  result := arr[..pos] + [elem] + arr[pos..];
  
  assert multiset(result) == multiset(arr[..pos] + [elem] + arr[pos..]);
  assert multiset(arr[..pos] + [elem] + arr[pos..]) == multiset(arr[..pos]) + multiset([elem]) + multiset(arr[pos..]);
  assert multiset(arr[..pos]) + multiset(arr[pos..]) == multiset(arr);
  assert multiset(result) == multiset(arr) + multiset{elem};
  
  forall i, j | 0 <= i < j < |result|
    ensures popcount(result[i]) <= popcount(result[j])
  {
    if i < pos && j == pos {
      assert result[i] == arr[i];
      assert result[j] == elem;
      assert popcount(arr[i]) <= popcount(elem);
    } else if i == pos && j > pos {
      assert result[i] == elem;
      assert result[j] == arr[j-1];
      if pos < |arr| {
        assert popcount(elem) <= popcount(arr[pos]);
        assert popcount(arr[pos]) <= popcount(arr[j-1]);
      }
    } else if i < pos && j > pos {
      assert result[i] == arr[i];
      assert result[j] == arr[j-1];
      assert popcount(arr[i]) <= popcount(arr[j-1]);
    } else if i < pos && j < pos {
      assert result[i] == arr[i];
      assert result[j] == arr[j];
      assert popcount(arr[i]) <= popcount(arr[j]);
    } else if i > pos && j > pos {
      assert result[i] == arr[i-1];
      assert result[j] == arr[j-1];
      assert popcount(arr[i-1]) <= popcount(arr[j-1]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Using fixed InsertSorted with proper multiset reasoning */
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
    invariant SortedByPopcount(sorted)
  {
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
    sorted := InsertSorted(sorted, s[i]);
    assert multiset(sorted) == multiset(s[..i]) + multiset{s[i]};
    assert multiset(sorted) == multiset(s[..i+1]);
    i := i + 1;
  }
  assert i == |s|;
  assert s[..i] == s;
  assert multiset(sorted) == multiset(s);
}
// </vc-code>
