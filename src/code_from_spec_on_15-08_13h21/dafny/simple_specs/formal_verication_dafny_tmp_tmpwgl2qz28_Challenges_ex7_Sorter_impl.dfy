datatype Bases = A | C | G | T


//ATOM

//checks if a sequence is in base order
predicate bordered(s:seq<Bases>)
{
  forall j, k :: 0 <= j < k < |s| ==> below(s[j], s[k])
}


//ATOM

//idea from Rustan Leino video "Basics of specification and verification: Lecture 3, the Dutch National Flag algorithm"
//modified for 4 elements
predicate below(first: Bases, second: Bases)
{
  first == second ||
  first == A || 
  (first == C && (second == G || second == T)) || 
  (first == G && second == T) ||
  second == T
}


//ATOM

//swaps two sequence indexes
method Exchanger(s: seq<Bases>, x:nat, y:nat) returns (t: seq<Bases>)
requires 0 < |s| && x < |s| && y < |s|
ensures |t| == |s|
ensures forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b]
ensures t[x] == s[y] && s[x] == t[y]
ensures multiset(s) == multiset(t)
{
  /* code modified by LLM (iteration 1): replaced assume statements with proper implementation */
  t := s[x := s[y]][y := s[x]];
}


//IMPL Sorter

method Sorter(bases: seq<Bases>) returns (sobases:seq<Bases>)
requires 0 < |bases|
ensures |sobases| == |bases|
ensures bordered(sobases)
ensures multiset(bases) == multiset(sobases)
{
  sobases := bases;
  var i := 0;
  
  while i < |sobases|
    invariant 0 <= i <= |sobases|
    invariant |sobases| == |bases|
    invariant multiset(sobases) == multiset(bases)
    invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
    /* code modified by LLM (iteration 1): added invariant to ensure sorted portion is minimal */
    invariant forall j, k :: 0 <= j < i && i <= k < |sobases| ==> below(sobases[j], sobases[k])
  {
    var minIdx := i;
    var j := i + 1;
    
    while j < |sobases|
      invariant i <= minIdx < |sobases|
      invariant i + 1 <= j <= |sobases|
      /* code modified by LLM (iteration 1): corrected inner loop invariant */
      invariant forall k :: i <= k < j ==> below(sobases[minIdx], sobases[k])
    {
      if !below(sobases[minIdx], sobases[j]) {
        minIdx := j;
      }
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): fixed swapping logic and added proper assertions */
    if minIdx != i {
      sobases := Exchanger(sobases, i, minIdx);
      
      /* code modified by LLM (iteration 1): added assertions to help prove invariant maintenance */
      assert forall k :: i < k < |sobases| ==> below(sobases[i], sobases[k]);
      assert forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k]);
      assert forall j :: 0 <= j < i ==> below(sobases[j], sobases[i]);
    }
    
    /* code modified by LLM (iteration 1): added assertion to help prove the updated invariant */
    assert forall j, k :: 0 <= j < k < i + 1 ==> below(sobases[j], sobases[k]);
    
    i := i + 1;
  }
}