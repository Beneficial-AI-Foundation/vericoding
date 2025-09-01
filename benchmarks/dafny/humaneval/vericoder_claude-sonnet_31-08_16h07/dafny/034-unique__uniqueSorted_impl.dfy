

// <vc-helpers>
lemma StrictOrderingPreserved(s: seq<int>, result: seq<int>, i: int, newElem: int)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    requires forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    requires 0 <= i <= |s|
    requires i > 0 ==> forall x :: x in result ==> x in s[0..i]
    requires i > 0 ==> forall x :: x in s[0..i] ==> x in result
    requires i == 0 ==> |result| == 0
    requires i < |s|
    requires newElem == s[i]
    requires i == 0 || s[i] != s[i-1]
    ensures forall k :: 0 <= k < |result| ==> result[k] < newElem
{
    if |result| > 0 && i > 0 {
        var lastIdx := |result| - 1;
        assert result[lastIdx] in s[0..i];
        assert exists j :: 0 <= j < i && result[lastIdx] == s[j];
        
        forall k | 0 <= k < |result|
            ensures result[k] < newElem
        {
            assert result[k] in s[0..i];
            assert exists j :: 0 <= j < i && result[k] == s[j];
            var j :| 0 <= j < i && result[k] == s[j];
            assert j < i;
            assert s[j] <= s[i];
            if s[j] == s[i] {
                assert result[k] == s[j] == s[i];
                assert result[k] in s[0..i];
                if i > 0 {
                    assert s[i] != s[i-1];
                    assert j != i-1;
                    if j < i-1 {
                        assert s[j] <= s[i-1] < s[i];
                        assert false;
                    }
                }
                assert j < i-1 || j == i-1;
                if j == i-1 {
                    assert s[j] == s[i-1] == s[i];
                    assert s[i] != s[i-1];
                    assert false;
                }
                assert j < i-1;
                assert s[j] <= s[i-1];
                assert s[i-1] < s[i];
                assert s[j] < s[i];
                assert false;
            }
            assert s[j] < s[i];
            assert result[k] < newElem;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    invariant i > 0 ==> forall x :: x in result ==> x in s[0..i]
    invariant i > 0 ==> forall x :: x in s[0..i] ==> x in result
    invariant i == 0 ==> |result| == 0
  {
    if i == 0 || s[i] != s[i-1] {
      StrictOrderingPreserved(s, result, i, s[i]);
      result := result + [s[i]];
    }
    i := i + 1;
  }
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}