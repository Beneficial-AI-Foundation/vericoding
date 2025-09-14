// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka

method MinOfMultiset( m: multiset<int> ) returns( min: int )
    ensures min in m;
    ensures forall z | z in m :: min <= z;
{
  assume{:axiom} false;
}

// Ekki má breyta þessu falli.


///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.

// <vc-helpers>
lemma RemoveAddMultiset<T>(m: multiset<T>, x: T)
  requires x in m
  ensures (m - multiset{x}) + multiset{x} == m
{
  assert (m - multiset{x}) + multiset{x} == m;
}

lemma LastBoundImpliesAllLe(s: seq<int>, z: int)
  requires |s| > 0
  requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
  requires s[|s|-1] <= z
  ensures forall p | 0 <= p < |s| :: s[p] <= z
{
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall p | 0 <= p < i :: s[p] <= z
  {
    if i == |s|-1 {
      assert s[i] <= z;
    } else {
      // i < |s|-1, so by sortedness s[i] <= s[|s|-1]
      assert 0 <= i < |s|;
      assert i < |s|-1 < |s|;
      assert s[i] <= s[|s|-1];
      assert s[|s|-1] <= z;
      assert s[i] <= z;
    }
    i := i + 1;
  }
  assert forall p | 0 <= p < |s| :: s[p] <= z;
}
// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
  var r := m;
  var res: seq<int> := [];
  while r != multiset{}
    invariant multiset(res) + r == m
    invariant forall p,q | 0 <= p < q < |res| :: res[p] <= res[q]
    invariant (|res| == 0) || (forall z | z in r :: res[|res|-1] <= z)
    decreases |r|
  {
    var v := MinOfMultiset(r);
    assert v in r;
    assert forall z | z in r :: v <= z;

    var oldRes := res;
    var oldR := r;

    res := oldRes + [v];
    r := oldR - multiset{v};

    assert multiset(res) == multiset(oldRes) + multiset{v};
    RemoveAddMultiset(oldR, v);
    assert (oldR - multiset{v}) + multiset{v} == oldR;

    assert multiset(oldRes) + oldR == m;
    assert multiset(res) + r == m;

    if |oldRes| > 0 {
      assert forall p,q | 0 <= p < q < |oldRes| :: oldRes[p] <= oldRes[q];
      assert forall z | z in oldR :: oldRes[|oldRes|-1] <= z;
      assert oldRes[|oldRes|-1] <= v;
      LastBoundImpliesAllLe(oldRes, v);
      assert forall p | 0 <= p < |oldRes| :: oldRes[p] <= v;
    }
    assert forall p,q | 0 <= p < q < |res| :: res[p] <= res[q];

    if |res| > 0 {
      assert forall z | z in r :: res[|res|-1] <= z;
    }
  }
  return res;
}
// </vc-code>

