// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 5): completed lemma body with inductive recursion to prove IsSorted and multiset preservation*/
lemma InsertIsSorted(x: int, s: seq<int>)
  requires IsSorted(s)
  ensures IsSorted(Insert(x, s))
  ensures multiset(Insert(x, s)) == multiset(s) + multiset{x}
{
  if |s| == 0 {
  } else if x <= s[0] {
  } else {
    InsertIsSorted(x, s[1..]);
  }
}

/* helper modified by LLM (iteration 5): completed lemma body with inductive recursion to prove IsSorted and multiset preservation for SortSeq */
lemma SortSeqIsSorted(s: seq<int>)
  ensures IsSorted(SortSeq(s))
  ensures multiset(SortSeq(s)) == multiset(s)
{
  if |s| == 0 {
  } else {
    SortSeqIsSorted(s[1..]);
    InsertIsSorted(s[0], SortSeq(s[1..]));
  }
}

function Insert(x: int, xs: seq<int>): seq<int>
{
  if |xs| == 0 || x <= xs[0] then [x] + xs else [xs[0]] + Insert(x, xs[1..])
}

function SortSeq(xs: seq<int>): seq<int>
{
  if |xs| == 0 then [] else Insert(xs[0], SortSeq(xs[1..]))
}
// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 5): simplified trueValues construction to avoid index errors */
  if |s| == 0 {
    sorted := [];
    return;
  }
  var trueValues := [];
  for i := 0 to |s|-1
  {
    if p[i]
    {
      trueValues := trueValues + [s[i]];
    }
  }
  var sortedTrue := SortSeq(trueValues);
  var index := 0;
  var result := [];
  for i := 0 to |s|-1
  {
    if p[i]
    {
      result := result + [sortedTrue[index]];
      index := index + 1;
    }
    else
    {
      result := result + [s[i]];
    }
  }
  sorted := result;
}
// </vc-code>
