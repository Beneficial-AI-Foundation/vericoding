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
  
  /* code modified by LLM (iteration 1): Fixed loop invariants and logic to correctly find minimum */
  while elements != multiset{}
    invariant elements <= m
    invariant min in m
    invariant forall z | z in (m - elements) :: min <= z
    decreases |elements|
  {
    var current :| current in elements;
    /* code modified by LLM (iteration 1): Update min if current is smaller */
    if current < min {
      min := current;
    }
    elements := elements - multiset{current};
  }
}