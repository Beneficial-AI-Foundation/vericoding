// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for non-decreasing sequence */
predicate NonDecreasing(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 5): recursive Min without let-in to avoid parse issues */
function Min(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0] else if s[0] < Min(s[1..]) then s[0] else Min(s[1..])
}

/* helper modified by LLM (iteration 5): RemoveOne implementation */
function RemoveOne(s: seq<int>, x: int): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else if s[0] == x then s[1..]
  else [s[0]] + RemoveOne(s[1..], x)
}

/* helper modified by LLM (iteration 5): MinProperty lemma */
lemma MinProperty(s: seq<int>)
  requires |s| > 0
  ensures Min(s) in s
  ensures forall y :: y in s ==> Min(s) <= y
  decreases |s|
{
  if |s| == 1 {
    // trivial: Min(s) == s[0]
  } else {
    var t := Min(s[1..]);
    MinProperty(s[1..]);
    if s[0] < t {
      assert Min(s) == s[0];
      assert Min(s) in s;
      forall y | y in s {
        if y == s[0] {
          assert Min(s) <= y;
        } else {
          assert y in s[1..];
          assert t <= y;
          assert Min(s) <= y;
        }
      }
    } else {
      // not (s[0] < t) implies s[0] >= t
      assert s[0] >= t;
      assert Min(s) == t;
      assert t in s[1..];
      forall y | y in s {
        if y == s[0] {
          assert t <= y;
        } else {
          assert y in s[1..];
          assert t <= y;
        }
      }
    }
  }
}

/* helper modified by LLM (iteration 5): RemoveOne_multiset lemma */
lemma RemoveOne_multiset(s: seq<int>, x: int)
  requires x in s
  ensures multiset(s) == multiset(RemoveOne(s, x)) + multiset([x])
  decreases |s|
{
  if |s| == 0 {
    // impossible due to requires
  } else {
    assert s == [s[0]] + s[1..];
    if s[0] == x {
      assert RemoveOne(s, x) == s[1..];
      assert multiset(s) == multiset([s[0]] + s[1..]);
      assert multiset([s[0]] + s[1..]) == multiset([s[0]]) + multiset(s[1..]);
      assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
      assert multiset([s[0]]) == multiset([x]);
      assert multiset(s) == multiset(RemoveOne(s, x)) + multiset([x]);
    } else {
      RemoveOne_multiset(s[1..], x);
      assert RemoveOne(s, x) == [s[0]] + RemoveOne(s[1..], x);
      assert multiset(RemoveOne(s, x)) == multiset([s[0]]) + multiset(RemoveOne(s[1..], x));
      // from inductive hypothesis: multiset(s[1..]) == multiset(RemoveOne(s[1..], x)) + multiset([x])
      assert multiset(s) == multiset([s[0]]) + multiset(s[1..]);
      assert multiset(s) == multiset([s[0]]) + (multiset(RemoveOne(s[1..], x)) + multiset([x]));
      assert multiset(s) == (multiset([s[0]]) + multiset(RemoveOne(s[1..], x))) + multiset([x]);
      assert multiset(s) == multiset(RemoveOne(s, x)) + multiset([x]);
    }
  }
}

/* helper modified by LLM (iteration 5): Min_remove_one_non_decreasing lemma */
lemma Min_remove_one_non_decreasing(s: seq<int>)
  requires |s| > 0
  ensures |RemoveOne(s, Min(s))| > 0 ==> Min(RemoveOne(s, Min(s))) >= Min(s)
  decreases |s|
{
  var m := Min(s);
  MinProperty(s); // so m in s and m <= every element of s
  if |s| == 1 {
    // RemoveOne will be empty; antecedent false
  } else {
    if s[0] == m {
      // RemoveOne(s,m) == s[1..]
      if |s[1..]| > 0 {
        assert RemoveOne(s, m) == s[1..];
        // m <= every element of s, in particular m <= Min(s[1..])
        MinProperty(s[1..]);
        assert m <= Min(s[1..]);
        assert Min(RemoveOne(s, m)) == Min(s[1..]);
        assert Min(RemoveOne(s, m)) >= m;
      }
    } else {
      // s[0] != m, so m is in s[1..]
      Min_remove_one_non_decreasing(s[1..]);
      if |RemoveOne(s[1..], m)| == 0 {
        // Then RemoveOne(s,m) == [s[0]]
        assert RemoveOne(s, m) == [s[0]];
        assert Min(RemoveOne(s, m)) == s[0];
        // m is min of s, so s[0] >= m
        assert s[0] >= m;
        assert Min(RemoveOne(s, m)) >= m;
      } else {
        // Both s[0] >= m and Min(RemoveOne(s[1..], m)) >= m, so min >= m
        assert Min(RemoveOne(s, m)) == if s[0] < Min(RemoveOne(s[1..], m)) then s[0] else Min(RemoveOne(s[1..], m));
        // from inductive call on s[1..]
        assert Min(RemoveOne(s[1..], m)) >= m;
        assert s[0] >= m;
        assert Min(RemoveOne(s, m)) >= m;
      }
    }
  }
}

/* helper modified by LLM (iteration 5): AppendKeepsSorted lemma */
lemma AppendKeepsSorted(sorted: seq<int>, m: int)
  requires NonDecreasing(sorted)
  requires |sorted| == 0 || sorted[|sorted|-1] <= m
  ensures NonDecreasing(sorted + [m])
{
  forall i, j | 0 <= i < j < |sorted + [m]| {
    if j < |sorted| {
      // both indices in the original sorted sequence
      assert sorted[i] <= sorted[j];
    } else {
      // j == |sorted|, i < |sorted|
      if i < |sorted| {
        assert sorted[i] <= sorted[|sorted|-1];
        assert sorted[|sorted|-1] <= m;
        assert sorted[i] <= m;
      }
    }
  }
}

// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): implement selection sort using Min and RemoveOne helpers with proper lemma calls */
  var res := [];
  var rest := s;
  while |rest| > 0
    invariant multiset(res) + multiset(rest) == multiset(s)
    invariant |res| + |rest| == |s|
    invariant NonDecreasing(res)
    invariant (|rest| == 0 || |res| == 0 || res[|res|-1] <= Min(rest))
  {
    var oldRest := rest;
    var m := Min(oldRest);
    MinProperty(oldRest); // m in oldRest and m <= elements of oldRest
    RemoveOne_multiset(oldRest, m);
    if |res| > 0 {
      AppendKeepsSorted(res, m);
    }
    Min_remove_one_non_decreasing(oldRest);
    res := res + [m];
    rest := RemoveOne(oldRest, m);
  }
  sorted := res;
}

// </vc-code>
