//IMPL 
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
    var s := m;
    min :| min in s;
    
    while s != multiset{}
        invariant s <= m
        invariant min in m
        /* code modified by LLM (iteration 1): Corrected invariant to ensure min is minimum of all elements processed so far */
        invariant forall z | z in (m - s) :: min <= z
        decreases |s|
    {
        var x :| x in s;
        s := s - multiset{x};
        /* code modified by LLM (iteration 1): Update min to maintain it as the minimum seen so far */
        if x < min {
            min := x;
        }
    }
}