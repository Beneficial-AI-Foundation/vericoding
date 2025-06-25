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
  var elements := m;
  min :| min in elements;
  
  while elements != multiset{}
    invariant min in m
    invariant forall z | z in (m - elements) :: min <= z
  {
    var current :| current in elements;
    if current < min {
      min := current;
    }
    elements := elements - multiset{current};
  }
}

//IMPL Sort
// Selection sort sem raðar poka í runu.
// Klárið að forrita þetta fall.
method Sort( m: multiset<int> ) returns ( s: seq<int> )
  // Setjið viðeigandi ensures klausur hér
  ensures multiset(s) == m
  ensures forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
{
  s := [];
  var remaining := m;
  
  while remaining != multiset{}
    invariant multiset(s) + remaining == m
    invariant forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
    invariant forall i | 0 <= i < |s| :: forall x | x in remaining :: s[i] <= x
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    decreases |remaining|
  {
    var min := MinOfMultiset(remaining);
    /* code modified by LLM (iteration 1): store old values for verification */
    var old_s := s;
    var old_remaining := remaining;
    
    s := s + [min];
    remaining := remaining - multiset{min};
    
    /* code modified by LLM (iteration 1): assertions to help verify invariants are maintained */
    assert multiset(old_s) + old_remaining == m;
    assert min in old_remaining;
    assert multiset([min]) == multiset{min};
    assert multiset(s) == multiset(old_s) + multiset([min]);
    assert multiset(s) == multiset(old_s) + multiset{min};
    assert multiset(s) + remaining == multiset(old_s) + multiset{min} + (old_remaining - multiset{min});
    assert multiset(s) + remaining == multiset(old_s) + old_remaining;
    assert multiset(s) + remaining == m;
    
    /* code modified by LLM (iteration 1): assertion to help verify sorted property */
    assert forall i | 0 <= i < |old_s| :: forall x | x in old_remaining :: old_s[i] <= x;
    assert forall z | z in old_remaining :: min <= z;
    assert forall i | 0 <= i < |old_s| :: old_s[i] <= min;
  }
}

//ATOM

// Ekki má breyta þessu falli.
method Test( m: multiset<int> )
{
}