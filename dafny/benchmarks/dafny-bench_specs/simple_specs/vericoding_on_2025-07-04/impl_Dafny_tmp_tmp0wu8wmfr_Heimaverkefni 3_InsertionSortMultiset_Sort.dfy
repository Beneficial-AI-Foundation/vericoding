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
  /* code modified by LLM (iteration 1): implemented binary search algorithm */
  var low := 0;
  var high := |s|;
  
  while low < high
    invariant 0 <= low <= high <= |s|
    invariant forall i | 0 <= i < low :: s[i] <= x
    invariant forall i | high <= i < |s| :: s[i] >= x
    decreases high - low
  {
    var mid := (low + high) / 2;
    if s[mid] <= x {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  k := low;
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
    
    var k := Search(r, x);
    /* code modified by LLM (iteration 1): added assertion to help verification */
    assert multiset(r[..k] + [x] + r[k..]) == multiset(r) + multiset{x};
    r := r[..k] + [x] + r[k..];
  }
}