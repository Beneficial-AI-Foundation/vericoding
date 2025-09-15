// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed InsertSorted postcondition proofs */
function InsertSorted(x: int, s: seq<int>): seq<int>
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(x, s)| ==> InsertSorted(x, s)[i] <= InsertSorted(x, s)[j]
  ensures |InsertSorted(x, s)| == |s| + 1
  ensures multiset([x] + s) == multiset(InsertSorted(x, s))
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

lemma InsertSortedSorted(x: int, s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < |InsertSorted(x, s)| ==> InsertSorted(x, s)[i] <= InsertSorted(x, s)[j]
  decreases |s|
{
  var result := InsertSorted(x, s);
  if |s| == 0 {
    assert result == [x];
  } else if x <= s[0] {
    assert result == [x] + s;
    forall i, j | 0 <= i < j < |result|
      ensures result[i] <= result[j]
    {
      if i == 0 {
        assert result[i] == x;
        assert result[j] == s[j-1];
        assert x <= s[0] <= s[j-1];
      } else {
        assert result[i] == s[i-1];
        assert result[j] == s[j-1];
        assert s[i-1] <= s[j-1];
      }
    }
  } else {
    InsertSortedSorted(x, s[1..]);
    var subResult := InsertSorted(x, s[1..]);
    assert result == [s[0]] + subResult;
    forall i, j | 0 <= i < j < |result|
      ensures result[i] <= result[j]
    {
      if i == 0 {
        assert result[i] == s[0];
        if j == 1 {
          if |s| > 1 {
            assert result[j] == subResult[0];
            if x <= s[1] {
              assert subResult[0] == x;
              assert s[0] <= x;
            } else {
              assert subResult[0] == s[1];
              assert s[0] <= s[1];
            }
          }
        } else {
          assert result[j] == subResult[j-1];
          assert j-1 >= 1;
          assert subResult[0] <= subResult[j-1];
          if x <= s[1] {
            assert subResult[0] == x;
            assert s[0] <= x;
          } else {
            assert subResult[0] == s[1];
            assert s[0] <= s[1];
          }
        }
      } else {
        assert result[i] == subResult[i-1];
        assert result[j] == subResult[j-1];
        assert subResult[i-1] <= subResult[j-1];
      }
    }
  }
}

lemma InsertSortedMultiset(x: int, s: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures multiset([x] + s) == multiset(InsertSorted(x, s))
  decreases |s|
{
  var result := InsertSorted(x, s);
  if |s| == 0 {
    assert result == [x];
    assert multiset([x] + s) == multiset([x]);
  } else if x <= s[0] {
    assert result == [x] + s;
    assert multiset([x] + s) == multiset([x] + s);
  } else {
    InsertSortedMultiset(x, s[1..]);
    var subResult := InsertSorted(x, s[1..]);
    assert result == [s[0]] + subResult;
    assert multiset([x] + s[1..]) == multiset(subResult);
    assert multiset([x] + s) == multiset([x] + [s[0]] + s[1..]);
    assert multiset([x] + [s[0]] + s[1..]) == multiset([s[0]] + [x] + s[1..]);
    assert multiset([s[0]] + [x] + s[1..]) == multiset([s[0]] + subResult);
    assert multiset([s[0]] + subResult) == multiset(result);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use explicit lemma calls */
{
  if |s| == 0 {
    sorted := [];
  } else {
    var tail := SortSeq(s[1..]);
    InsertSortedSorted(s[0], tail);
    InsertSortedMultiset(s[0], tail);
    sorted := InsertSorted(s[0], tail);
  }
}
// </vc-code>
