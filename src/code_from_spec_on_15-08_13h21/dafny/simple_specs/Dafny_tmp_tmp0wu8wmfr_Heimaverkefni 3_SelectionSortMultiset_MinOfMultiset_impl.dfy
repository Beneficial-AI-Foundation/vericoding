// IMPL
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
  var elements := m;
  min :| min in elements;
  
  while elements != multiset{}
    invariant min in m
    /* code modified by LLM (iteration 1): Added invariant to maintain relationship between elements and original multiset */
    invariant elements <= m
    invariant forall z | z in m && z !in elements :: min <= z
    decreases |elements|
  {
    var x :| x in elements;
    elements := elements - multiset{x};
    if x < min {
      /* code modified by LLM (iteration 1): Added assertion to help verify that x is in m */
      assert x in m;
      min := x;
    }
  }
}