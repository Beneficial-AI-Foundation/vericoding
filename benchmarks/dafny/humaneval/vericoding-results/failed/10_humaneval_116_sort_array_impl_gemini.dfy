// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
predicate IsSortedByPopcount(s: seq<nat>) {
  forall i, j :: 0 <= i < j < |s| ==> popcount(s[i]) <= popcount(s[j])
}

function Insert(x: nat, s: seq<nat>): seq<nat>
  requires IsSortedByPopcount(s)
{
  if s == [] then [x]
  else if popcount(x) <= popcount(s[0]) then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

/* helper modified by LLM (iteration 5): added proof body for recursive case */
lemma {:induction s} LemmaInsertMultiset(x: nat, s: seq<nat>)
  requires IsSortedByPopcount(s)
  ensures multiset(Insert(x, s)) == multiset(s) + multiset({x})
{
  if s != [] && popcount(x) > popcount(s[0]) {
    assert IsSortedByPopcount(s[1..]);
    LemmaInsertMultiset(x, s[1..]);
  }
}

/* helper modified by LLM (iteration 5): added proof details for all cases */
lemma {:induction s} LemmaInsertSorted(x: nat, s: seq<nat>)
  requires IsSortedByPopcount(s)
  ensures IsSortedByPopcount(Insert(x, s))
{
  if s == [] {
  } else if popcount(x) <= popcount(s[0]) {
    assert forall i :: 0 <= i < |s| ==> popcount(s[0]) <= popcount(s[i]);
  } else { // popcount(x) > popcount(s[0])
    assert IsSortedByPopcount(s[1..]);
    LemmaInsertSorted(x, s[1..]);
    var t := Insert(x, s[1..]);
    if t != [] {
      if s[1..] == [] {
        assert t[0] == x;
        assert popcount(s[0]) < popcount(t[0]);
      } else {
        if popcount(x) <= popcount(s[1]) {
          assert t[0] == x;
          assert popcount(s[0]) < popcount(t[0]);
        } else {
          assert t[0] == s[1];
          assert popcount(s[0]) <= popcount(t[0]);
        }
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): no changes needed; errors stemmed from helpers */
  var res: seq<nat> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSortedByPopcount(res)
    invariant multiset(res) == multiset(s[..i])
    invariant |res| == i
  {
    var x := s[i];
    LemmaInsertSorted(x, res);
    LemmaInsertMultiset(x, res);
    res := Insert(x, res);
    i := i + 1;
  }
  sorted := res;
}
// </vc-code>
