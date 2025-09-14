// <vc-preamble>
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate MultisetEquiv(s1: seq<int>, s2: seq<int>)
{
    multiset(s1) == multiset(s2)
}
method MergeSortedAux(a: seq<int>, b: seq<int>) returns (result: seq<int>)
{
    assume {:axiom} false;
    result := [];
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive merge function and correctness lemma */
function MergeSeq(a: seq<int>, b: seq<int>): seq<int>
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + MergeSeq(a[1..], b)
  else [b[0]] + MergeSeq(a, b[1..])
}
lemma MergeSeq_Correct(a: seq<int>, b: seq<int>)
  requires IsSorted(a) && IsSorted(b)
  decreases |a| + |b|
  ensures IsSorted(MergeSeq(a,b))
  ensures MultisetEquiv(MergeSeq(a,b), a + b)
{
  if |a| == 0 {
    // MergeSeq(a,b) == b, properties follow
  } else if |b| == 0 {
    // MergeSeq(a,b) == a, properties follow
  } else if a[0] <= b[0] {
    MergeSeq_Correct(a[1..], b);
    assert MergeSeq(a,b) == [a[0]] + MergeSeq(a[1..], b);
    if |MergeSeq(a[1..], b)| == 0 {
      // tail empty
    } else {
      var t := MergeSeq(a[1..], b)[0];
      if |a[1..]| == 0 {
        // then MergeSeq(a[1..], b) == b
        assert t == b[0];
        assert a[0] <= t;
      } else {
        // both a[1..] and b non-empty; head of MergeSeq(a[1..],b) is either a[1] or b[0]
        if a[1] <= b[0] {
          assert t == a[1];
          assert a[0] <= a[1];
          assert a[0] <= t;
        } else {
          assert t == b[0];
          assert a[0] <= b[0];
          assert a[0] <= t;
        }
      }
    }
    // tail is sorted by recursive call, so whole is sorted
    // Multiset reasoning
    assert a == [a[0]] + a[1..];
    assert multiset(a + b) == multiset(([a[0]] + a[1..]) + b);
    assert multiset(([a[0]] + a[1..]) + b) == multiset([a[0]]) + multiset(a[1..] + b);
    assert multiset(MergeSeq(a[1..], b)) == multiset(a[1..] + b);
    assert multiset([a[0]] + MergeSeq(a[1..], b)) == multiset([a[0]]) + multiset(MergeSeq(a[1..], b));
    assert multiset([a[0]]) + multiset(a[1..] + b) == multiset(a + b);
  } else {
    MergeSeq_Correct(a, b[1..]);
    assert MergeSeq(a,b) == [b[0]] + MergeSeq(a, b[1..]);
    if |MergeSeq(a, b[1..])| == 0 {
      // tail empty
    } else {
      var t := MergeSeq(a, b[1..])[0];
      if |b[1..]| == 0 {
        // then MergeSeq(a, b[1..]) == a
        assert t == a[0];
        assert b[0] <= t;
      } else {
        if b[1] <= a[0] {
          assert t == b[1];
          assert b[0] <= b[1];
          assert b[0] <= t;
        } else {
          assert t == a[0];
          assert b[0] <= a[0];
          assert b[0] <= t;
        }
      }
    }
    // Multiset reasoning symmetric
    assert b == [b[0]] + b[1..];
    assert multiset(a + b) == multiset(a + ([b[0]] + b[1..]));
    assert multiset(a + ([b[0]] + b[1..])) == multiset(a) + multiset([b[0]] + b[1..]);
    assert multiset([b[0]] + b[1..]) == multiset([b[0]]) + multiset(b[1..]);
    assert multiset(MergeSeq(a, b[1..])) == multiset(a + b[1..]);
    assert multiset([b[0]] + MergeSeq(a, b[1..])) == multiset([b[0]]) + multiset(MergeSeq(a, b[1..]));
    assert multiset([b[0]]) + multiset(MergeSeq(a, b[1..])) == multiset(a + b);
  }
}

// </vc-helpers>

// <vc-spec>
method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires IsSorted(a)
    requires IsSorted(b)
    ensures IsSorted(result)
    ensures MultisetEquiv(result, a + b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): call MergeSeq and apply correctness lemma */
  result := MergeSeq(a, b);
  MergeSeq_Correct(a, b);
}

// </vc-code>
