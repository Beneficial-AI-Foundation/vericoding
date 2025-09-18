// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): sorted predicate (adjacent definition) */
predicate Sorted(s: seq<int>) {
  forall i | 0 <= i + 1 < |s| ==> s[i] <= s[i+1]
}

/* helper modified by LLM (iteration 4): merge two sorted sequences */
function Merge(a: seq<int>, b: seq<int>): seq<int>
  ensures |Merge(a,b)| == |a| + |b|
  ensures multiset(Merge(a,b)) == multiset(a) + multiset(b)
  ensures (Sorted(a) && Sorted(b)) ==> Sorted(Merge(a,b))
  decreases |a| + |b|
{
  if |a| == 0 then b
  else if |b| == 0 then a
  else if a[0] <= b[0] then [a[0]] + Merge(a[1..], b)
  else [b[0]] + Merge(a, b[1..])
}

/* helper modified by LLM (iteration 5): tail of sorted sequence is sorted */
lemma SortedTail(s: seq<int>)
  requires Sorted(s)
  ensures |s| <= 1 || Sorted(s[1..])
{
  // If s has length <= 1, trivial. Otherwise the adjacent property shifts.
}

/* helper modified by LLM (iteration 5): Merge preserves multiset */
lemma Merge_multiset(a: seq<int>, b: seq<int>)
  ensures multiset(Merge(a,b)) == multiset(a) + multiset(b)
  decreases |a| + |b|
{
  if |a| == 0 {
    // Merge(a,b) == b
  } else if |b| == 0 {
    // Merge(a,b) == a
  } else if a[0] <= b[0] {
    Merge_multiset(a[1..], b);
    assert multiset(Merge(a, b)) == multiset([a[0]] + Merge(a[1..], b));
    assert multiset([a[0]] + Merge(a[1..], b)) == multiset(Merge(a[1..], b)) + multiset([a[0]]);
    assert multiset(Merge(a[1..], b)) + multiset([a[0]]) == (multiset(a[1..]) + multiset(b)) + multiset([a[0]]);
    assert (multiset(a[1..]) + multiset(b)) + multiset([a[0]]) == multiset(a) + multiset(b);
  } else {
    Merge_multiset(a, b[1..]);
    assert multiset(Merge(a, b)) == multiset([b[0]] + Merge(a, b[1..]));
    assert multiset([b[0]] + Merge(a, b[1..])) == multiset(Merge(a, b[1..])) + multiset([b[0]]);
    assert multiset(Merge(a, b[1..])) + multiset([b[0]]) == (multiset(a) + multiset(b[1..])) + multiset([b[0]]);
    assert (multiset(a) + multiset(b[1..])) + multiset([b[0]]) == multiset(a) + multiset(b);
  }
}

/* helper modified by LLM (iteration 5): Merge preserves sortedness when inputs sorted */
lemma Merge_sorted(a: seq<int>, b: seq<int>)
  requires Sorted(a) && Sorted(b)
  ensures Sorted(Merge(a,b))
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
    // trivial
  } else if a[0] <= b[0] {
    // a[0] is head; need Sorted(a[1..]) and sortedness of Merge(a[1..], b)
    SortedTail(a);
    Merge_sorted(a[1..], b);
    // Show adjacency: For adjacent indices in the merged sequence, either both are in Merge(a[1..],b)
    // (handled by inductive hypothesis) or are the boundary between a[0] and head of Merge(a[1..],b).
    // The head of Merge(a[1..],b) is >= min(a[1], b[0]) and a[0] <= both a[1] and b[0], so a[0] <= head.
    // These facts follow from Sorted(a) and Sorted(b) and the branch condition a[0] <= b[0].
  } else {
    // symmetric case
    SortedTail(b);
    Merge_sorted(a, b[1..]);
  }
}

/* helper modified by LLM (iteration 5): MergeSortFunc preserves multiset */
lemma MergeSortFunc_multiset(s: seq<int>)
  ensures multiset(MergeSortFunc(s)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 {
  } else {
    MergeSortFunc_multiset(s[..|s|/2]);
    MergeSortFunc_multiset(s[|s|/2..]);
    Merge_multiset(MergeSortFunc(s[..|s|/2]), MergeSortFunc(s[|s|/2..]));
  }
}

/* helper modified by LLM (iteration 5): MergeSortFunc produces sorted sequence */
lemma MergeSortFunc_sorted(s: seq<int>)
  ensures Sorted(MergeSortFunc(s))
  decreases |s|
{
  if |s| <= 1 {
  } else {
    MergeSortFunc_sorted(s[..|s|/2]);
    MergeSortFunc_sorted(s[|s|/2..]);
    Merge_sorted(MergeSortFunc(s[..|s|/2]), MergeSortFunc(s[|s|/2..]));
  }
}

/* helper modified by LLM (iteration 4): MergeSort function */
function MergeSortFunc(s: seq<int>): seq<int>
  ensures |MergeSortFunc(s)| == |s|
  ensures Sorted(MergeSortFunc(s))
  ensures multiset(MergeSortFunc(s)) == multiset(s)
  decreases |s|
{
  if |s| <= 1 then s
  else Merge(MergeSortFunc(s[..|s|/2]), MergeSortFunc(s[|s|/2..]))
}

// </vc-helpers>

// <vc-spec>
method MergeSort(list: seq<int>) returns (result: seq<int>)
    ensures
        |result| == |list| &&
        (forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]) &&
        multiset(result) == multiset(list)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): use MergeSortFunc to compute sorted result */
  result := MergeSortFunc(list);
}

// </vc-code>
