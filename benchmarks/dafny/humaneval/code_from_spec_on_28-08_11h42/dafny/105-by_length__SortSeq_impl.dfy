method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  // post-conditions-start
  ensures |result| <= |arr|
  ensures forall i :: 0 <= i < |result| ==>
    result[i] in ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedProperty(s: seq<int>, sorted: seq<int>)
  requires |sorted| == |s|
  requires multiset(s) == multiset(sorted)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] in multiset(s)
{
}

lemma InsertionSortPreservesMultiset(s: seq<int>, i: int, sorted: seq<int>)
  requires 0 <= i <= |s|
  requires |sorted| == i
  requires multiset(sorted) == multiset(s[..i])
  requires forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
  ensures i < |s| ==> multiset(sorted + [s[i]]) == multiset(s[..i+1])
{
  if i < |s| {
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]};
    assert multiset(sorted + [s[i]]) == multiset(sorted) + multiset{s[i]};
  }
}

lemma MultisetSliceLemma(sorted: seq<int>, pos: int)
  requires 0 <= pos <= |sorted|
  ensures multiset(sorted) == multiset(sorted[..pos]) + multiset(sorted[pos..])
{
  if pos == 0 {
    assert sorted[..pos] == [];
    assert sorted[pos..] == sorted;
    assert multiset(sorted[..pos]) == multiset{};
    assert multiset(sorted) == multiset{} + multiset(sorted);
  } else if pos == |sorted| {
    assert sorted[..pos] == sorted;
    assert sorted[pos..] == [];
    assert multiset(sorted[pos..]) == multiset{};
    assert multiset(sorted) == multiset(sorted) + multiset{};
  } else {
    assert sorted == sorted[..pos] + sorted[pos..];
    assert multiset(sorted) == multiset(sorted[..pos] + sorted[pos..]);
    assert multiset(sorted[..pos] + sorted[pos..]) == multiset(sorted[..pos]) + multiset(sorted[pos..]);
  }
}

lemma InsertPreservesMultiset(sorted: seq<int>, x: int, result: seq<int>, pos: int)
  requires 0 <= pos <= |sorted|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires result == sorted[..pos] + [x] + sorted[pos..]
  requires forall j :: 0 <= j < pos ==> sorted[j] <= x
  requires pos < |sorted| ==> x <= sorted[pos]
  ensures multiset(result) == multiset(sorted) + multiset{x}
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
{
  assert multiset(result) == multiset(sorted[..pos] + [x] + sorted[pos..]);
  assert multiset(sorted[..pos] + [x] + sorted[pos..]) == multiset(sorted[..pos]) + multiset{x} + multiset(sorted[pos..]);
  MultisetSliceLemma(sorted, pos);
  assert multiset(result) == multiset(sorted) + multiset{x};
  
  forall i, j | 0 <= i < j < |result|
    ensures result[i] <= result[j]
  {
    if i < pos && j < pos {
      assert result[i] == sorted[i];
      assert result[j] == sorted[j];
      assert sorted[i] <= sorted[j];
    } else if i < pos && j == pos {
      assert result[i] == sorted[i];
      assert result[j] == x;
      assert sorted[i] <= x;
    } else if i < pos && j > pos {
      assert result[i] == sorted[i];
      assert result[j] == sorted[j-1];
      assert sorted[i] <= x;
      assert x <= sorted[j-1];
      assert sorted[i] <= sorted[j-1];
    } else if i == pos && j > pos {
      assert result[i] == x;
      assert result[j] == sorted[j-1];
      assert x <= sorted[j-1];
    } else if i > pos && j > pos {
      assert result[i] == sorted[i-1];
      assert result[j] == sorted[j-1];
      assert sorted[i-1] <= sorted[j-1];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |sorted| == i
    invariant multiset(sorted) == multiset(s[..i])
    invariant forall j, k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
  {
    InsertionSortPreservesMultiset(s, i, sorted);
    var x := s[i];
    var pos := 0;
    while pos < |sorted| && sorted[pos] <= x
      invariant 0 <= pos <= |sorted|
      invariant forall j :: 0 <= j < pos ==> sorted[j] <= x
      invariant pos < |sorted| ==> x < sorted[pos] || sorted[pos] <= x
    {
      pos := pos + 1;
    }
    assert forall j :: 0 <= j < pos ==> sorted[j] <= x;
    assert pos < |sorted| ==> x < sorted[pos];
    var newSorted := sorted[..pos] + [x] + sorted[pos..];
    InsertPreservesMultiset(sorted, x, newSorted, pos);
    sorted := newSorted;
    i := i + 1;
  }
  assert multiset(sorted) == multiset(s[..|s|]);
  assert s[..|s|] == s;
  assert multiset(sorted) == multiset(s);
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end