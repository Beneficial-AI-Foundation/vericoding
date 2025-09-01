function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
function contains(s: seq<int>, x: int): bool
  reads s
  decreases |s|
{
  if |s| == 0 then false
  else s[0] == x || contains(s[1..], x)
}

lemma lemma_count_rec_contains_iff(a: seq<int>, x: int)
  ensures (count_rec(a, x) > 0) == contains(a, x)
  decreases |a|
{
  if |a| == 0 {
  } else {
    lemma_count_rec_contains_iff(a[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s: set<int> := {};
  var res: seq<int> := [];

  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |res| ==> res[j] !in res[..j]
    invariant forall j :: 0 <= j < |res| ==> contains(a, res[j])
    invariant forall j :: 0 <= j < i ==> a[j] in s || (count_rec(a, a[j]) == 1 && a[j] in res)
    invariant forall x_in_s :: x_in_s in s ==> x_in_s in a[..i]
    invariant forall j :: 0 <= j < |res| ==> res[j] !in s
    invariant forall k :: 0 <= k < |res| ==> count_rec(a, res[k]) == 1
    invariant forall x :: x in s <==> (x in a[..i] && count_rec(a,x) > 1)
    invariant forall x :: x in res <==> (x in a[..i] && count_rec(a,x) == 1)

  {
    lemma_count_rec_contains_iff(a, a[i]);
    if count_rec(a, a[i]) == 1 {
      if !(a[i] in res) { // already in result?
        res := res + [a[i]];
      }
    } else {
      if !(a[i] in s) {
        s := s + {a[i]};
      }
    }
  }

  result := [];
  for k := 0 to |a|-1
    invariant 0 <= k <= |a|
    invariant forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
    invariant forall i :: 0 <= i < |result| ==> result[i] !in result[..i]
    invariant forall i :: 0 <= i < |result| ==> contains(a, result[i])
    invariant forall x :: x in result <==> (x in a[..k] && count_rec(a,x) == 1)
  {
    lemma_count_rec_contains_iff(a, a[k]);
    if count_rec(a, a[k]) == 1 {
      if !(a[k] in result) {
        result := result + [a[k]];
      }
    }
  }
}
// </vc-code>

method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}