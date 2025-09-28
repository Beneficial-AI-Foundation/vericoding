// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define non-decreasing predicate by popcount */
function is_non_decreasing_by_popcount(s: seq<nat>): bool
{
  if |s| <= 1 then true
  else popcount(s[0]) <= popcount(s[1]) && is_non_decreasing_by_popcount(s[1..])
}

/* helper modified by LLM (iteration 2): insertion into a sequence ordered by popcount */
function insert(x: nat, t: seq<nat>): seq<nat>
  decreases |t|
{
  if |t| == 0 then [x]
  else if popcount(x) <= popcount(t[0]) then [x] + t
  else [t[0]] + insert(x, t[1..])
}

/* helper modified by LLM (iteration 2): insertion sort by popcount */
function sortByPopcount(s: seq<nat>): seq<nat>
  decreases |s|
{
  if |s| == 0 then []
  else insert(s[0], sortByPopcount(s[1..]))
}

/* helper modified by LLM (iteration 2): properties of insert regarding multiset and length */
lemma InsertProperties(x: nat, t: seq<nat>)
  ensures multiset(insert(x, t)) == multiset([x]) + multiset(t)
  ensures |insert(x, t)| == |t| + 1
  decreases |t|
{
  if |t| == 0 {
  } else if popcount(x) <= popcount(t[0]) {
  } else {
    InsertProperties(x, t[1..]);
  }
}

/* helper modified by LLM (iteration 2): insert preserves non-decreasing order by popcount */
lemma InsertPreservesNonDec(x: nat, t: seq<nat>)
  requires is_non_decreasing_by_popcount(t)
  ensures is_non_decreasing_by_popcount(insert(x, t))
  decreases |t|
{
  if |t| == 0 {
  } else if popcount(x) <= popcount(t[0]) {
    // [x] + t is non-decreasing since popcount(x) <= popcount(t[0]) and t is non-decreasing
  } else {
    // result is [t0] + insert(x, t1)
    InsertPreservesNonDec(x, t[1..]);
    if |t| == 1 {
      assert popcount(t[0]) <= popcount(x);
    } else {
      if popcount(x) <= popcount(t[1]) {
        assert popcount(t[0]) < popcount(x);
        assert popcount(t[0]) <= popcount(x);
      } else {
        assert popcount(t[0]) <= popcount(t[1]);
      }
    }
  }
}

/* helper modified by LLM (iteration 2): sorting preserves multiset/length and yields non-decreasing sequence by popcount */
lemma SortProperties(s: seq<nat>)
  ensures is_non_decreasing_by_popcount(sortByPopcount(s))
  ensures |sortByPopcount(s)| == |s|
  ensures multiset(sortByPopcount(s)) == multiset(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    SortProperties(s[1..]);
    InsertPreservesNonDec(s[0], sortByPopcount(s[1..]));
    InsertProperties(s[0], sortByPopcount(s[1..]));
    assert s == [s[0]] + s[1..];
  }
}

/* helper modified by LLM (iteration 2): suffix of a non-decreasing sequence remains non-decreasing */
lemma SuffixNonDec(s: seq<nat>, k: int)
  requires 0 <= k <= |s|
  requires is_non_decreasing_by_popcount(s)
  ensures is_non_decreasing_by_popcount(s[k..])
  decreases k
{
  if k == 0 {
  } else {
    if |s| <= 1 {
    } else {
      assert is_non_decreasing_by_popcount(s[1..]);
    }
    SuffixNonDec(s[1..], k - 1);
  }
}

/* helper modified by LLM (iteration 2): from non-decreasing property, get pairwise popcount order */
lemma NonDecImpliesPairwiseFor(s: seq<nat>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires is_non_decreasing_by_popcount(s)
  ensures popcount(s[i]) <= popcount(s[j])
  decreases j - i
{
  if j == i + 1 {
    SuffixNonDec(s, i);
    assert |s[i..]| == |s| - i;
    assert i + 1 < |s|;
    assert |s[i..]| >= 2;
    assert popcount((s[i..])[0]) <= popcount((s[i..])[1]);
    assert (s[i..])[0] == s[i];
    assert (s[i..])[1] == s[i+1];
    assert popcount(s[i]) <= popcount(s[j]);
  } else {
    NonDecImpliesPairwiseFor(s, i, j - 1);
    SuffixNonDec(s, j - 1);
    assert |s[j-1..]| == |s| - (j - 1);
    assert j < |s|;
    assert |s[j-1..]| >= 2;
    assert popcount((s[j-1..])[0]) <= popcount((s[j-1..])[1]);
    assert (s[j-1..])[0] == s[j-1];
    assert (s[j-1..])[1] == s[j];
    assert popcount(s[j - 1]) <= popcount(s[j]);
    assert popcount(s[i]) <= popcount(s[j]);
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
  /* code modified by LLM (iteration 2): implement insertion sort by popcount and prove ensures */
  sorted := sortByPopcount(s);
  SortProperties(s);
  assert is_non_decreasing_by_popcount(sorted);
  forall i: int, j: int | 0 <= i < j < |sorted| {
    NonDecImpliesPairwiseFor(sorted, i, j);
    assert popcount(sorted[i]) <= popcount(sorted[j]);
  }
}
// </vc-code>
