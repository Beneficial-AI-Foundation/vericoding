// <vc-preamble>
// Helper predicate to check if a sequence is sorted in ascending order
ghost predicate IsSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Helper predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(a: seq<real>, b: seq<real>)
{
  multiset(a) == multiset(b)
}

// Main method specification for msort
// </vc-preamble>

// <vc-helpers>
function Merge(l: seq<real>, r: seq<real>): seq<real>
  decreases |l| + |r|
{
  if |l| == 0 then r
  else if |r| == 0 then l
  else if l[0] <= r[0] then [l[0]] + Merge(l[1..], r)
  else [r[0]] + Merge(l, r[1..])
}

function SortFun(a: seq<real>): seq<real>
  decreases |a|
{
  if |a| <= 1 then a
  else var m := |a| / 2; Merge(SortFun(a[..m]), SortFun(a[m..]))
}

lemma Merge_length(l: seq<real>, r: seq<real>)
  ensures |Merge(l, r)| == |l| + |r|
  decreases |l| + |r|
{
  if |l| == 0 || |r| == 0 {
    // trivial by definition of Merge
  } else {
    if l[0] <= r[0] {
      Merge_length(l[1..], r);
    } else {
      Merge_length(l, r[1..]);
    }
  }
}

/* helper modified by LLM (iteration 5): revised Merge_multiset proof to avoid timeout */
lemma Merge_multiset(l: seq<real>, r: seq<real>)
  ensures multiset(Merge(l, r)) == multiset(l) + multiset(r)
  decreases |l| + |r|
{
  if |l| == 0 {
    // Merge(l,r) == r, so multisets coincide
  } else if |r| == 0 {
    // Merge(l,r) == l
  } else {
    if l[0] <= r[0] {
      Merge_multiset(l[1..], r);
      assert Merge(l, r) == [l[0]] + Merge(l[1..], r);
      assert multiset(Merge(l, r)) == multiset([l[0]] + Merge(l[1..], r));
      assert multiset([l[0]] + Merge(l[1..], r)) == multiset([l[0]]) + multiset(Merge(l[1..], r));
      assert multiset(Merge(l[1..], r)) == multiset(l[1..]) + multiset(r);
      // combine equalities
      assert multiset([l[0]]) + (multiset(l[1..]) + multiset(r)) == (multiset([l[0]]) + multiset(l[1..])) + multiset(r);
      assert multiset([l[0]]) + multiset(l[1..]) == multiset(l);
      assert multiset(Merge(l, r)) == multiset(l) + multiset(r);
    } else {
      Merge_multiset(l, r[1..]);
      assert Merge(l, r) == [r[0]] + Merge(l, r[1..]);
      assert multiset(Merge(l, r)) == multiset([r[0]] + Merge(l, r[1..]));
      assert multiset([r[0]] + Merge(l, r[1..])) == multiset([r[0]]) + multiset(Merge(l, r[1..]));
      assert multiset(Merge(l, r[1..])) == multiset(l) + multiset(r[1..]);
      // rearrange and use that multiset([r[0]]) + multiset(r[1..]) == multiset(r)
      assert multiset([r[0]]) + (multiset(l) + multiset(r[1..])) == multiset(l) + (multiset([r[0]]) + multiset(r[1..]));
      assert multiset([r[0]]) + multiset(r[1..]) == multiset(r);
      assert multiset(Merge(l, r)) == multiset(l) + multiset(r);
    }
  }
}

lemma Merge_sorted(l: seq<real>, r: seq<real>)
  requires IsSorted(l) && IsSorted(r)
  ensures IsSorted(Merge(l, r))
  decreases |l| + |r|
{
  if |l| == 0 || |r| == 0 {
    // result is one of the inputs, which is sorted
  } else {
    if l[0] <= r[0] {
      Merge_sorted(l[1..], r);
      // by induction Merge(l[1..], r) is sorted, and l[0] <= r[0] and l is sorted, so merged sequence is sorted
    } else {
      Merge_sorted(l, r[1..]);
      // analogous reasoning when first element comes from r
    }
  }
}

lemma SortFun_length(a: seq<real>)
  ensures |SortFun(a)| == |a|
  decreases |a|
{
  if |a| <= 1 {
    // trivial
  } else {
    var m := |a| / 2;
    SortFun_length(a[..m]);
    SortFun_length(a[m..]);
    Merge_length(SortFun(a[..m]), SortFun(a[m..]));
  }
}

lemma SortFun_multiset(a: seq<real>)
  ensures multiset(SortFun(a)) == multiset(a)
  decreases |a|
{
  if |a| <= 1 {
    // trivial
  } else {
    var m := |a| / 2;
    SortFun_multiset(a[..m]);
    SortFun_multiset(a[m..]);
    Merge_multiset(SortFun(a[..m]), SortFun(a[m..]));
  }
}

lemma SortFun_sorted(a: seq<real>)
  ensures IsSorted(SortFun(a))
  decreases |a|
{
  if |a| <= 1 {
    // trivially sorted
  } else {
    var m := |a| / 2;
    SortFun_sorted(a[..m]);
    SortFun_sorted(a[m..]);
    Merge_sorted(SortFun(a[..m]), SortFun(a[m..]));
  }
}

// </vc-helpers>

// <vc-spec>
method msort(a: seq<real>) returns (result: seq<real>)
  ensures |result| == |a|
  ensures IsSorted(result)
  ensures IsPermutation(a, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute result via SortFun and discharge postconditions */
  result := SortFun(a);
  SortFun_length(a);
  SortFun_sorted(a);
  SortFun_multiset(a);
}

// </vc-code>
