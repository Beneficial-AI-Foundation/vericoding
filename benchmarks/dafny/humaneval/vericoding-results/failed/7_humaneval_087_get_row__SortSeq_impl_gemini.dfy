// <vc-preamble>
type SortSeqState = seq<(int, int)>
function less(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  x < u || (x == u && y > v)
}
function less_eq(a: (int, int), b: (int, int)): bool {
  var (x, y) := a; var (u, v) := b;
  (x == u && y == v) || less(a, b)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added lemmas about the ordering to help the verifier */
predicate Sorted(s: SortSeqState)
{
  forall i, j :: 0 <= i < j < |s| ==> less_eq(s[i], s[j])
}

lemma lemma_less_implies_less_eq(a: (int, int), b: (int, int))
  requires less(a, b)
  ensures less_eq(a, b)
{
}

lemma lemma_total_order(a: (int, int), b: (int, int))
  ensures less(a, b) || a == b || less(b, a)
{
}

lemma lemma_not_less_is_less_eq(a: (int, int), b: (int, int))
  requires !less(a, b)
  ensures less_eq(b, a)
{
  lemma_total_order(a, b);
}

lemma lemma_less_eq_transitive(a: (int, int), b: (int, int), c: (int, int))
  requires less_eq(a, b)
  requires less_eq(b, c)
  ensures less_eq(a, c)
{
}

lemma lemma_SortedAfterInsert(s: SortSeqState, x: (int, int), j: int)
  requires Sorted(s)
  requires 0 <= j <= |s|
  requires forall k :: 0 <= k < j ==> less_eq(s[k], x)
  requires forall k :: j <= k < |s| ==> less_eq(x, s[k])
  ensures Sorted(s[..j] + [x] + s[j..])
{
}

/* helper modified by LLM (iteration 5): provided proof for multiset lemma */
lemma lemma_MultisetInsert<T>(s: seq<T>, x: T, j: int)
  requires 0 <= j <= |s|
  ensures multiset(s[..j] + [x] + s[j..]) == multiset(s) + multiset([x])
{
  calc {
    multiset(s[..j] + [x] + s[j..]);
    == multiset(s[..j]) + multiset([x] + s[j..]);
    == multiset(s[..j]) + (multiset([x]) + multiset(s[j..]));
    == (multiset(s[..j]) + multiset(s[j..])) + multiset([x]);
    == multiset(s[..j] + s[j..]) + multiset([x]);
    == multiset(s) + multiset([x]);
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: SortSeqState) returns (sorted: SortSeqState)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> less_eq(sorted[i], sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added assert to help prove multiset invariant */
  sorted := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant Sorted(sorted)
    invariant |sorted| == i
    invariant multiset(s) == multiset(sorted) + multiset(s[i..])
  {
    var x := s[i];
    
    var j: int := 0;
    while j < |sorted| && less(sorted[j], x)
      invariant 0 <= j <= |sorted|
      invariant forall k :: 0 <= k < j ==> less(sorted[k], x)
    {
      j := j + 1;
    }

    forall k | 0 <= k < j
      ensures less_eq(sorted[k], x)
    {
      lemma_less_implies_less_eq(sorted[k], x);
    }
    
    if j < |sorted| {
      lemma_not_less_is_less_eq(sorted[j], x);
    }
    
    forall k | j <= k < |sorted|
        ensures less_eq(x, sorted[k])
    {
        if k > j {
            lemma_less_eq_transitive(x, sorted[j], sorted[k]);
        }
    }

    lemma_SortedAfterInsert(sorted, x, j);
    
    lemma_MultisetInsert(sorted, x, j);
    sorted := sorted[..j] + [x] + sorted[j..];

    assert s[i..] == [s[i]] + s[i+1..];
    
    i := i + 1;
  }
}
// </vc-code>
