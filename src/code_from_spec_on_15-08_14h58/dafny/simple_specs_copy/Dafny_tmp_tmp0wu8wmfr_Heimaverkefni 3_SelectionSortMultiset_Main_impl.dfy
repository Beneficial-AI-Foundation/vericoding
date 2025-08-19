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
    invariant forall x | x in s :: forall y | y in remaining :: x <= y
  {
    var min := MinOfMultiset(remaining);
    /* code modified by LLM (iteration 2): Added assertions to establish key properties before update */
    assert forall y | y in remaining :: min <= y;
    assert forall x | x in s :: x <= min;
    
    /* code modified by LLM (iteration 2): Prove that appending min maintains sortedness */
    if |s| > 0 {
      assert s[|s|-1] <= min;
    }
    
    s := s + [min];
    remaining := remaining - multiset{min};
    
    /* code modified by LLM (iteration 2): Help prove the sortedness property for the updated sequence */
    assert forall p | 0 <= p < |s|-1 :: s[p] <= s[|s|-1];
    assert forall p,q | 0 <= p < q < |s|-1 :: s[p] <= s[q];
  }
}

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
    invariant forall z | z in m && z !in elements :: min <= z
    invariant elements <= m
  {
    var current :| current in elements;
    if current < min {
      min := current;
    }
    elements := elements - multiset{current};
  }
}

//ATOM

method Main()
{
  var m := multiset{0,1,2,3,4,5,6,7,8,9,0,1,2,3,4,5,6,7,8,9};
  var s := Sort(m);
  print s;
}