/* code modified by LLM (iteration 1): implemented proper minimum finding logic to replace assume statements */
method MinOfMultiset( m: multiset<int> ) returns( min: int )
  requires m != multiset{}
  ensures min in m
  ensures forall z | z in m :: min <= z
{
  // Convert multiset to sequence to iterate through elements
  var elements: seq<int> := [];
  var temp := m;
  
  // Extract all elements from multiset into sequence
  while temp != multiset{}
    invariant multiset(elements) <= m
    invariant temp + multiset(elements) == m
    decreases |temp|
  {
    var x :| x in temp;
    elements := elements + [x];
    temp := temp - multiset{x};
  }
  
  // Find minimum in the sequence
  min := elements[0];
  var i := 1;
  
  while i < |elements|
    invariant 1 <= i <= |elements|
    invariant min in multiset(elements)
    invariant forall j | 0 <= j < i :: min <= elements[j]
    decreases |elements| - i
  {
    if elements[i] < min {
      min := elements[i];
    }
    i := i + 1;
  }
  
  // The postconditions follow from the loop invariants and multiset(elements) == m
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
    invariant forall i | 0 <= i < |s| :: forall x | x in remaining :: s[i] <= x
    decreases |remaining|
  {
    var min := MinOfMultiset(remaining);
    /* code modified by LLM (iteration 1): replaced sequence concatenation with proper sequence construction and added verification assertions */
    s := s + [min];
    remaining := remaining - multiset{min};
    
    /* code modified by LLM (iteration 1): added assertion to help verify that the minimum element maintains sorted order */
    assert forall i | 0 <= i < |s|-1 :: s[i] <= min;
  }
}