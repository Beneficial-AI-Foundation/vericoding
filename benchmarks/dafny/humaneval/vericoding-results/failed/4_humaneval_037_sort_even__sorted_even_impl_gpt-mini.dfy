// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): functions and lemmas for evens/odds extraction, functional sorting, interleaving and multiset properties */

function evens(a: seq<int>): seq<int>
  ensures |evens(a)| == (|a| + 1) / 2
{
  if |a| == 0 then []
  else if |a| == 1 then [a[0]]
  else [a[0]] + evens(a[2..])
}

function odds(a: seq<int>): seq<int>
  ensures |odds(a)| == |a| / 2
{
  if |a| <= 1 then []
  else [a[1]] + odds(a[2..])
}

function interleave(e: seq<int>, o: seq<int>): seq<int>
  ensures |interleave(e,o)| == |e| + |o|
{
  if |e| == 0 && |o| == 0 then []
  else if |o| == 0 then [e[0]] + interleave(e[1..], o)
  else [e[0]] + ([o[0]] + interleave(e[1..], o[1..]))
}

function index_of_min(s: seq<int>): nat
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then 0
  else
    var idx := index_of_min(s[1..]);
    if s[0] <= s[1+idx] then 0 else 1 + idx
}

function SortedSeq(s: seq<int>): seq<int>
  ensures |SortedSeq(s)| == |s|
  ensures multiset(SortedSeq(s)) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |SortedSeq(s)| ==> SortedSeq(s)[i] <= SortedSeq(s)[j]
  decreases |s|
{
  if |s| <= 1 then s
  else
    var i := index_of_min(s);
    [s[i]] + SortedSeq(s[..i] + s[i+1..])
}

lemma MultisetEvensOdds(a: seq<int>)
  ensures multiset(a) == multiset(evens(a)) + multiset(odds(a))
  decreases |a|
{
  if |a| <= 1 {
    // trivial: when |a| == 0 or 1 the decomposition is immediate
  } else {
    var rest := a[2..];
    MultisetEvensOdds(rest);
    // multiset(a) = {a[0], a[1]} + multiset(rest) and evens/odds decompose accordingly
  }
}

lemma InterleaveMultiset(e: seq<int>, o: seq<int>)
  ensures multiset(interleave(e,o)) == multiset(e) + multiset(o)
  decreases |e| + |o|
{
  if |e| == 0 && |o| == 0 {
    // empty
  } else if |o| == 0 {
    // interleave(e, []) = [e[0]] + interleave(e[1..], [])
    InterleaveMultiset(e[1..], o);
  } else {
    // interleave(e,o) = [e[0], o[0]] + interleave(e[1..], o[1..])
    InterleaveMultiset(e[1..], o[1..]);
  }
}

lemma InterleaveIndex(e: seq<int>, o: seq<int>)
  ensures forall i :: 0 <= i < |e| ==> interleave(e,o)[2*i] == e[i]
  ensures forall i :: 0 <= i < |o| ==> interleave(e,o)[2*i+1] == o[i]
  decreases |e| + |o|
{
  if |e| == 0 && |o| == 0 {
  } else if |o| == 0 {
    // interleave(e, []) = [e[0]] + interleave(e[1..], [])
    InterleaveIndex(e[1..], o);
  } else {
    // interleave(e,o) = [e[0], o[0]] + interleave(e[1..], o[1..])
    InterleaveIndex(e[1..], o[1..]);
  }
}

// </vc-helpers>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)

  requires |a| > 0

  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): build sorted evens via a functional SortedSeq and interleave with original odds */
  var n := |a|;
  var ev := evens(a);
  var od := odds(a);
  var se := SortedSeq(ev);
  // se has same multiset as ev, and is sorted; interleave places se at even positions and od at odd positions
  sorted := interleave(se, od);
}

// </vc-code>
