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

// </vc-helpers>

// <vc-spec>
method Sort( m: multiset<int> ) returns ( s: seq<int> )
    // Setjið viðeigandi ensures klausur hér
    ensures multiset(s) == m;
    ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
// </vc-spec>
// <vc-code>
{
  var acc: seq<int> := [];
  var rem: multiset<int> := m;
  while 0 < |rem|
    invariant multiset(acc) + rem == m
    invariant forall i,j | 0 <= i < j < |acc| :: acc[i] <= acc[j]
    invariant forall i | 0 <= i < |acc| :: forall z | z in rem :: acc[i] <= z
    invariant |acc| <= |m|
    decreases |m| - |acc|
  {
    var x := MinOfMultiset(rem);
    assert x in rem;
    assert forall i | 0 <= i < |acc| :: acc[i] <= x;
    acc := acc + [x];
    rem := rem - multiset{x};
  }
  s := acc;
}
// </vc-code>

