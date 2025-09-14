method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma MultisetMembership<T>(s: seq<T>, x: T)
    ensures x in s <==> x in multiset(s)
{
    if |s| == 0 {
        assert x !in s;
        assert x !in multiset(s);
    } else {
        if x == s[0] {
            assert x in s;
            assert multiset(s)[x] >= 1;
            assert x in multiset(s);
        } else if x in s {
            assert exists i :: 1 <= i < |s| && s[i] == x;
            var i :| 1 <= i < |s| && s[i] == x;
            assert s[1..][i-1] == x;
            assert x in s[1..];
            MultisetMembership(s[1..], x);
            assert x in multiset(s[1..]);
            assert multiset(s) == multiset{s[0]} + multiset(s[1..]);
            assert x in multiset(s);
        } else if x in multiset(s) {
            if multiset(s)[x] > 0 {
                assert exists i :: 0 <= i < |s| && s[i] == x;
                assert x in s;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(s);
  result := uniqueSorted(sorted);
  
  // Prove the postconditions using the multiset property
  forall x | x in result
    ensures x in s
  {
    assert x in sorted;  // by uniqueSorted's postcondition
    MultisetMembership(sorted, x);
    assert x in multiset(sorted);
    assert multiset(sorted) == multiset(s);  // by SortSeq's postcondition
    assert x in multiset(s);
    MultisetMembership(s, x);
    assert x in s;
  }
  
  forall x | x in s
    ensures x in result
  {
    MultisetMembership(s, x);
    assert x in multiset(s);
    assert multiset(s) == multiset(sorted);  // by SortSeq's postcondition
    assert x in multiset(sorted);
    MultisetMembership(sorted, x);
    assert x in sorted;
    assert x in result;  // by uniqueSorted's postcondition
  }
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}