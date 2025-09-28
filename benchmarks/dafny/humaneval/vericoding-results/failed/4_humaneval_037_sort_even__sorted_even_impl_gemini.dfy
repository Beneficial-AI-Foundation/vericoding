// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [add lemmas to aid integer arithmetic proofs] */
lemma DivHelper(len: nat)
  ensures forall i:nat :: i < (len + 1) / 2 ==> 2 * i < len
  ensures forall i:nat :: i < len && i % 2 == 0 ==> i / 2 < (len + 1) / 2
{
}

predicate is_sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function insert(x: int, s: seq<int>): seq<int>
  requires is_sorted(s)
  ensures is_sorted(insert(x, s))
  ensures |insert(x, s)| == |s| + 1
  ensures multiset(insert(x, s)) == multiset(s) + multiset{x}
  // This postcondition strengthens the induction hypothesis, allowing the is_sorted postcondition to be proved.
  ensures |insert(x,s)| > 0 ==> forall y :: y in multiset(insert(x,s)) ==> insert(x,s)[0] <= y
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + insert(x, s[1..])
}

function sort(s: seq<int>): seq<int>
  ensures is_sorted(sort(s))
  ensures |sort(s)| == |s|
  ensures multiset(sort(s)) == multiset(s)
{
  if |s| == 0 then []
  else insert(s[0], sort(s[1..]))
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
  /* code modified by LLM (iteration 5): [call arithmetic helper lemma] */
  DivHelper(|a|);
  var num_evens := (|a| + 1) / 2;
  var evens := seq(num_evens, (i: int) => a[2 * i]);
  var sorted_evens := sort(evens);

  sorted := seq(|a|, (i: int) =>
    if i % 2 == 1 then a[i] else sorted_evens[i / 2]
  );
}

// </vc-code>
