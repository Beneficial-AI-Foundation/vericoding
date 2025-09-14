// <vc-preamble>
predicate InArray(a: array<int>, x: int)
    reads a
{
    exists i :: 0 <= i < a.Length && a[i] == x
}
// </vc-preamble>

// <vc-helpers>
function arrayToSet(ar: array<int>): set<int>
    reads ar
{
    set i | 0 <= i < ar.Length :: ar[i]
}

/* helper modified by LLM (iteration 3): removed invalid reads clause from lemma */
lemma InArrayVsInSet(ar: array<int>, x: int)
    ensures InArray(ar, x) <==> x in arrayToSet(ar)
{
}

/* helper modified by LLM (iteration 5): added lemma to help prove set equality invariant */
lemma SetDifferenceLemma<T>(A: set<T>, B: set<T>, x: T)
    requires x in B
    requires B <= A
    ensures (A - B) + {x} == A - (B - {x})
{
}
// </vc-helpers>

// <vc-spec>
method DissimilarElements(a: array<int>, b: array<int>) returns (result: seq<int>)

    ensures forall x :: x in result ==> (InArray(a, x) != InArray(b, x))

    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added helper lemma call to prove set invariant */
  var set_a := arrayToSet(a);
  var set_b := arrayToSet(b);
  var diff_set := (set_a - set_b) + (set_b - set_a);
  
  result := [];
  var remaining := diff_set;

  while remaining != {}
    invariant forall x :: x in result ==> (InArray(a, x) != InArray(b, x))
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    invariant remaining <= diff_set
    invariant (set x | x in result) == diff_set - remaining
  {
    var x :| x in remaining;

    SetDifferenceLemma(diff_set, remaining, x);
    
    InArrayVsInSet(a, x);
    InArrayVsInSet(b, x);
    
    result := result + [x];
    remaining := remaining - {x};
  }
}
// </vc-code>
