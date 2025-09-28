// <vc-preamble>
function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
function count_iter(a: seq<int>, x: int): int
{
  if |a| == 0 then 0
  else (if a[0] == x then 1 else 0) + count_iter(a[1..], x)
}

lemma count_equivalence(a: seq<int>, x: int)
  ensures count_rec(a, x) == count_iter(a, x)
{
  if |a| == 0 {
  } else {
    count_equivalence(a[1..], x);
  }
}

predicate appears_once(a: seq<int>, x: int)
{
  count_rec(a, x) == 1
}

predicate no_duplicates(s: seq<int>, a: seq<int>)
{
  forall i :: 0 <= i < |s| ==> appears_once(a, s[i])
}

function filter_unique(a: seq<int>, processed: seq<int>): seq<int>
{
  if |a| == 0 then []
  else if count_rec(a, a[0]) == 1 && a[0] !in processed
    then [a[0]] + filter_unique(a[1..], processed + [a[0]])
    else filter_unique(a[1..], processed)
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)

  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1

  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |result| ==> count_rec(a, result[j]) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in result <==> count_rec(a, a[j]) == 1)
  {
    if count_rec(a, a[i]) == 1 && a[i] !in result {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
