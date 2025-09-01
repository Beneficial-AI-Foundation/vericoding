function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
function contains(s: seq<int>, x: int): bool
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

lemma lemma_append_distinct(s: seq<int>, x: int)
  requires forall i :: 0 <= i < |s| ==> s[i] != x
  ensures forall i :: 0 <= i < |s + [x]| ==> (s + [x])[i] !in (s + [x])[..i]
{
  if |s| > 0 {
    assert (s + [x])[|s|] == x;
    assert (s + [x])[..|s|] == s[..];
  }
}

lemma lemma_append_contains(a: seq<int>, s: seq<int>, x: int)
  requires contains(a, x)
  requires forall i :: 0 <= i < |s| ==> contains(a, s[i])
  ensures forall i :: 0 <= i < |s + [x]| ==> contains(a, (s + [x])[i])
{}

lemma lemma_append_count_rec_1(a: seq<int>, s: seq<int>, x: int)
  requires count_rec(a, x) == 1
  requires forall i :: 0 <= i < |s| ==> count_rec(a, s[i]) == 1
  ensures forall i :: 0 <= i < |s + [x]| ==> count_rec(a, (s + [x])[i]) == 1
{}

lemma lemma_value_in_a_implies_value_in_res_or_s(a: seq<int>, i: int, x: int, res: seq<int>, s: set<int>)
  requires 0 <= i <= |a|
  requires forall x_res :: x_res in res <==> (x_res in a[..i] && count_rec(a,x_res) == 1)
  requires forall x_s :: x_s in s <==> (x_s in a[..i] && count_rec(a,x_s) > 1)
  decreases i
  ensures (x in a[..i] && count_rec(a, x) == 1) ==> x in res
  ensures (x in a[..i] && count_rec(a, x) > 1) ==> x in s
  ensures (x in a[..i] && count_rec(a, x) == 0) ==> !(x in res) && !(x in s)
{}
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
    invariant forall j :: 0 <= j < |res| ==> count_rec(a, res[j]) == 1
    invariant forall x :: x in s <==> (x in a[..i] && count_rec(a,x) > 1)
    invariant forall x :: x in res <==> (x in a[..i] && count_rec(a,x) == 1)
  {
    lemma_count_rec_contains_iff(a[..i], a[i]);
    if count_rec(a, a[i]) == 1 {
      if !(a[i] in res) {
        lemma_append_distinct(res, a[i]);
        lemma_append_contains(a, res, a[i]);
        lemma_append_count_rec_1(a, res, a[i]);
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
    invariant forall x :: x in result <==> (x in a[..k] && count_rec(a,x) == 1)
    invariant forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
    invariant forall i :: 0 <= i < |result| ==> result[i] !in result[..i]
    invariant forall i :: 0 <= i < |result| ==> contains(a,result[i])
  {
    lemma_count_rec_contains_iff(a[..k], a[k]);
    if count_rec(a, a[k]) == 1 {
      if !(a[k] in result) {
        lemma_append_distinct(result, a[k]);
        lemma_append_contains(a, result, a[k]);
        lemma_append_count_rec_1(a, result, a[k]);
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