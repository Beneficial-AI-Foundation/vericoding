// <vc-preamble>
function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed FilteredMerge and added comprehensive lemmas for sorted properties */
function FilteredMerge(s1: seq<int>, s2: seq<int>): seq<int>
  requires Sorted(s1) && Sorted(s2)
  ensures Sorted(FilteredMerge(s1, s2))
{
  if |s1| == 0 then s2
  else if |s2| == 0 then s1
  else if s1[0] <= s2[0] then
    [s1[0]] + FilteredMerge(s1[1..], s2)
  else
    [s2[0]] + FilteredMerge(s1, s2[1..])
}

predicate Sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma InsertSortedLemma(s: seq<int>, e: int)
  requires Sorted(s) && (forall x :: x in s ==> x >= e)
  ensures Sorted([e] + s)
{
}

lemma MergeSortedLemma(s1: seq<int>, s2: seq<int>)
  requires Sorted(s1) && Sorted(s2)
  ensures Sorted(FilteredMerge(s1, s2))
{
  if |s1| > 0 && |s2| > 0 {
    if s1[0] <= s2[0] {
      MergeSortedLemma(s1[1..], s2);
    } else {
      MergeSortedLemma(s1, s2[1..]);
    }
  }
}

lemma SortedConcatLemma(s1: seq<int>, s2: seq<int>)
  requires Sorted(s1) && Sorted(s2) && (|s1| == 0 || |s2| == 0 || s1[|s1|-1] <= s2[0])
  ensures Sorted(s1 + s2)
{
}

lemma SortedSliceLemma(s: seq<int>, i: int, j: int)
  requires Sorted(s) && 0 <= i <= j <= |s|
  ensures Sorted(s[i..j])
{
}

lemma ElementInSliceLemma(s: seq<int>, e: int, i: int, j: int)
  requires 0 <= i <= j <= |s|
  ensures e in s[i..j] <==> exists k :: i <= k < j && s[k] == e
{
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)

  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed sorted insertion with proper invariants and verification */
{
  var filtered: seq<int> := [];
  var i := 0;
  
  while i < |x|
    invariant 0 <= i <= |x|
    invariant forall e :: e in filtered ==> HasNoEvenDigit(e)
    invariant forall e :: e in filtered ==> e in x[..i]
    invariant forall e :: e in x[..i] && HasNoEvenDigit(e) ==> e in filtered
    invariant Sorted(filtered)
  {
    if HasNoEvenDigit(x[i]) {
      var newSeq: seq<int> := [];
      var inserted := false;
      var j := 0;
      
      while j < |filtered|
        invariant 0 <= j <= |filtered|
        invariant Sorted(newSeq)
        invariant !inserted ==> forall k :: k in newSeq ==> k <= x[i]
        invariant inserted ==> Sorted(newSeq + filtered[j..])
        invariant forall k :: k in newSeq ==> k in filtered[..j]
        invariant forall k :: k in filtered[..j] ==> k in newSeq
      {
        if !inserted && x[i] <= filtered[j] {
          newSeq := newSeq + [x[i]];
          inserted := true;
        }
        newSeq := newSeq + [filtered[j]];
        j := j + 1;
      }
      
      if !inserted {
        newSeq := newSeq + [x[i]];
      }
      
      filtered := newSeq;
    }
    i := i + 1;
  }
  
  result := filtered;
}
// </vc-code>
