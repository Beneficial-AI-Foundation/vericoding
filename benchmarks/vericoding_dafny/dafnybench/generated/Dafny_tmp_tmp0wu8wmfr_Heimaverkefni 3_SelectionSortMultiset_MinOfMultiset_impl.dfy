// Höfundur spurningar:  Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:     Alexander Guðmundsson
// Permalink lausnar:    https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method MinOfMultiset( m: multiset<int> ) returns( min: int )
    requires m != multiset{};
    ensures min in m;
    ensures forall z | z in m :: min <= z;
// </vc-spec>
// <vc-code>
{
  var s := m;
  min :| min in s;
  
  while s != multiset{}
    invariant min in m;
    invariant forall z | z in (m - s) :: min <= z;
    invariant s <= m;
    invariant forall z | z in s :: min <= z;
    decreases |s|;
  {
    var x :| x in s;
    s := s - multiset{x};
    if x < min {
      min := x;
    }
  }
}
// </vc-code>

// Ekki má breyta þessu falli.


///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.