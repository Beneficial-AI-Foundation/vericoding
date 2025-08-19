//ATOM
// Höfundur spurningar: Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/dtcnY

// Höfundur lausnar:   Alexander Guðmundsson
// Permalink lausnar:  https://rise4fun.com/Dafny/ybUCz

///////////////////////////////////////////////////////////////
// Hér byrjar óbreytanlegi hluti skrárinnar.
// Fyrir aftan þann hluta er sá hluti sem þið eigið að breyta.
///////////////////////////////////////////////////////////////

// Hjálparfall sem finnur minnsta gildi í poka
method MinOfMultiset( m: multiset<int> ) returns( min: int )
  requires m != multiset{}
  ensures min in m
  ensures forall z | z in m :: min <= z
{
  min := 0;
  assume min in m;
  assume forall z | z in m :: min <= z;
  return min;
}


// SPEC

///////////////////////////////////////////////////////////////
// Hér lýkur óbreytanlega hluta skrárinnar.
// Hér fyrir aftan er sá hluti sem þið eigið að breyta til að
// útfæra afbrigði af selection sort.
///////////////////////////////////////////////////////////////

//IMPL Selection sort sem raðar poka í runu
method Sort( m: multiset<int> ) returns ( s: seq<int> )
  ensures multiset(s) == m
  ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
{
  s := [];
  var remaining := m;
  
  while remaining != multiset{}
    invariant multiset(s) + remaining == m
    invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant forall i | 0 <= i < |s| :: forall z | z in remaining :: s[i] <= z
    decreases |remaining|
  {
    /* code modified by LLM (iteration 1): Store the size before modification to help with termination proof */
    var old_size := |remaining|;
    var min := MinOfMultiset(remaining);
    s := s + [min];
    remaining := remaining - multiset{min};
    /* code modified by LLM (iteration 1): Use stored size instead of old() for termination proof */
    assert |remaining| < old_size;
  }
}