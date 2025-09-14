// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate sorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

function insert(x: int, s: seq<int>): seq<int>
  requires sorted(s)
  ensures sorted(insert(x, s))
  ensures multiset(insert(x,s)) == multiset{x} + multiset(s)
  ensures |insert(x,s)| == |s| + 1
{
  if s == [] then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + insert(x, s[1..])
}

function sort(s: seq<int>): seq<int>
  ensures sorted(sort(s))
  ensures multiset(sort(s)) == multiset(s)
  ensures |sort(s)| == |s|
{
  if s == [] then []
  else insert(s[0], sort(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method sort_third(a: seq<int>) returns (sorted_even: seq<int>)

  requires |a| > 0

  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
// </vc-spec>
// <vc-code>
{
  var thirds := seq((|a| + 2) / 3, i => a[i * 3]);
  var sorted_thirds := sort(thirds);
  sorted_even := seq(|a|, i => if i % 3 == 0 then sorted_thirds[i / 3] else a[i]);
}
// </vc-code>
