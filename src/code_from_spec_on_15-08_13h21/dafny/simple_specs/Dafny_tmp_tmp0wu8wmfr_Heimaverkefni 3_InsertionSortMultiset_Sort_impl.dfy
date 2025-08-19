//ATOM
// Höfundur spurningar: Snorri Agnarsson, snorri@hi.is
// Permalink spurningar: https://rise4fun.com/Dafny/G4sc3

// Höfundur lausnar:   Alexander Guðmundsson
// Permalink lausnar:  https://rise4fun.com/Dafny/nujsu

// Insertion sort með hjálp helmingunarleitar.

method Search( s: seq<int>, x: int ) returns ( k: int )
  // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
  requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q]
  ensures 0 <= k <= |s|
  ensures forall i | 0 <= i < k :: s[i] <= x
  ensures forall i | k <= i < |s| :: s[i] >= x
  ensures forall z | z in s[..k] :: z <= x
  ensures forall z | z in s[k..] :: z >= x
  ensures s == s[..k]+s[k..]
{
  /* code modified by LLM (iteration 1): implemented binary search to find insertion position */
  var left := 0;
  var right := |s|;
  
  while left < right
    invariant 0 <= left <= right <= |s|
    invariant forall i | 0 <= i < left :: s[i] <= x
    invariant forall i | right <= i < |s| :: s[i] >= x
    decreases right - left
  {
    var mid := (left + right) / 2;
    if s[mid] <= x {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  k := left;
  
  /* code modified by LLM (iteration 1): added assertions to help prove postconditions */
  assert forall i | 0 <= i < k :: s[i] <= x;
  assert forall i | k <= i < |s| :: s[i] >= x;
  assert s[..k] == s[0..k];
  assert s[k..] == s[k..|s|];
}

//IMPL Sort
method Sort( m: multiset<int> ) returns ( r: seq<int> )
  ensures multiset(r) == m
  ensures forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
{
  r := [];
  var remaining := m;
  
  while remaining != multiset{}
    invariant multiset(r) + remaining == m
    invariant forall p,q | 0 <= p < q < |r| :: r[p] <= r[q]
    decreases |remaining|
  {
    var x :| x in remaining;
    remaining := remaining - multiset{x};
    
    var pos := Search(r, x);
    
    /* code modified by LLM (iteration 1): added assertions to help prove sortedness is maintained */
    assert forall i | 0 <= i < pos :: r[i] <= x;
    assert forall i | pos <= i < |r| :: r[i] >= x;
    
    r := r[..pos] + [x] + r[pos..];
    
    /* code modified by LLM (iteration 1): added assertion to help prove sortedness after insertion */
    assert forall p,q | 0 <= p < q < |r| :: r[p] <= r[q];
  }
}