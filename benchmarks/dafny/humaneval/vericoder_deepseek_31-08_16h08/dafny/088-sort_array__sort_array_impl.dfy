

// <vc-helpers>
function reverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else reverseSeq(s[1..]) + [s[0]]
}

lemma reverseSeqProperties(s: seq<int>)
  ensures |reverseSeq(s)| == |s|
  ensures forall k :: 0 <= k < |s| ==> reverseSeq(s)[k] == s[|s| - 1 - k]
{
  if |s| > 0 {
    reverseSeqProperties(s[1..]);
  }
}

function sortSeq(s: seq<int>): seq<int>
  decreases |s|
  ensures |sortSeq(s)| == |s|
  ensures multiset(s) == multiset(sortSeq(s))
  ensures forall i, j :: 0 <= i < j < |sortSeq(s)| ==> sortSeq(s)[i] <= sortSeq(s)[j]
{
  if |s| == 0 then []
  else
    var m := min(s);
    var rest := removeOne(s, m);
    [m] + sortSeq(rest)
}

function min(s: seq<int>): int
  requires |s| > 0
  ensures result in s
  ensures forall x :: x in s ==> result <= x
{
  if |s| == 1 then s[0]
  else
    var m := min(s[1..]);
    if s[0] <= m then s[0] else m
}

lemma minLemma(s: seq<int>)
  requires |s| > 0
  ensures min(s) in s
  ensures forall x :: x in s ==> min(s) <= x
{
  if |s| == 1 {
  } else {
    minLemma(s[1..]);
  }
}

function removeOne(s: seq<int>, x: int): seq<int>
  requires x in s
  ensures |removeOne(s, x)| == |s| - 1
  ensures multiset(removeOne(s, x)) == multiset(s) - multiset{x}
{
  if s[0] == x then s[1..]
  else [s[0]] + removeOne(s[1..], x)
}

lemma removeOneLemma(s: seq<int>, x: int)
  requires x in s
  ensures multiset(removeOne(s, x)) == multiset(s) - multiset{x}
  ensures |removeOne(s, x)| == |s| - 1
{
  if s[0] == x {
  } else {
    removeOneLemma(s[1..], x);
  }
}

lemma sortSeqDescendingLemma(s: seq<int>)
  ensures |sortSeqDescending(s)| == |s|
  ensures multiset(s) == multiset(sortSeqDescending(s))
  ensures forall i, j :: 0 <= i < j < |sortSeqDescending(s)| ==> sortSeqDescending(s)[i] >= sortSeqDescending(s)[j]
{
  var asc := sortSeq(s);
  reverseSeqProperties(asc);
}

function sortSeqDescending(s: seq<int>): seq<int>
  ensures |sortSeqDescending(s)| == |s|
  ensures multiset(s) == multiset(sortSeqDescending(s))
  ensures forall i, j :: 0 <= i < j < |sortSeqDescending(s)| ==> sortSeqDescending(s)[i] >= sortSeqDescending(s)[j]
{
  reverseSeq(sortSeq(s))
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| == 0 {
    sorted := [];
  } else if (s[0] + s[|s| - 1]) % 2 == 0 {
    sorted := sortSeqDescending(s);
  } else {
    sorted := sortSeq(s);
  }
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}