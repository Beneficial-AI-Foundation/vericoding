//ATOM
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

//IMPL Sort
// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
method Sort( m: multiset<int> ) returns ( s: seq<int> )
  // Setjið viðeigandi ensures klausur hér
  ensures multiset(s) == m
  ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
{
  /* code modified by LLM (iteration 1): Implement proper selection sort without relying on MinOfMultiset with assumes */
  s := [];
  var remaining := m;
  
  while remaining != multiset{}
    invariant multiset(s) + remaining == m
    invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant forall i | 0 <= i < |s| :: forall x | x in remaining :: s[i] <= x
    decreases |remaining|
  {
    /* code modified by LLM (iteration 1): Find minimum element directly without using MinOfMultiset */
    var min: int;
    var found := false;
    
    // Find any element first to initialize min
    var temp_remaining := remaining;
    while temp_remaining != multiset{} && !found
      decreases |temp_remaining|
    {
      // Extract an arbitrary element
      var arbitrary :| arbitrary in temp_remaining;
      min := arbitrary;
      found := true;
    }
    
    // Now find the actual minimum
    temp_remaining := remaining;
    while temp_remaining != multiset{}
      invariant found ==> min in remaining
      invariant found ==> forall x | x in remaining && x in (remaining - temp_remaining) :: min <= x
      decreases |temp_remaining|
    {
      var current :| current in temp_remaining;
      if found && current < min {
        min := current;
      } else if !found {
        min := current;
        found := true;
      }
      temp_remaining := temp_remaining - multiset{current};
    }
    
    s := s + [min];
    remaining := remaining - multiset{min};
  }
}

//ATOM
// Ekki má breyta þessu falli.
method Test( m: multiset<int> )
{
}