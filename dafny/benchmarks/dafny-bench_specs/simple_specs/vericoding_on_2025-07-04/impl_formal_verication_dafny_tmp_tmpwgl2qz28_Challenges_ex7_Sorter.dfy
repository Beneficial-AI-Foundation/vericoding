//ATOM
// see pdf 'ex6 & 7 documentation' for excercise question

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
  t := [];
  assume |t| == |s|;
  assume forall b:nat :: 0 <= b < |s| && b != x && b != y ==> t[b] == s[b];
  assume t[x] == s[y] && s[x] == t[y];
  assume multiset(s) == multiset(t);
  return t;
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
    /* code modified by LLM (iteration 1): Fixed invariant to properly express that elements 0..i-1 are sorted */
    invariant forall j, k :: 0 <= j < k < i ==> below(sobases[j], sobases[k])
    /* code modified by LLM (iteration 1): Added invariant to ensure elements 0..i-1 are <= all elements i..|sobases| */
    invariant forall j, k :: 0 <= j < i <= k < |sobases| ==> below(sobases[j], sobases[k])
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < |sobases|
      invariant i <= minIndex < |sobases|
      invariant i < j <= |sobases|
      /* code modified by LLM (iteration 1): Fixed invariant to correctly express that minIndex points to minimum element in range i..j-1 */
      invariant forall k :: i <= k < j ==> below(sobases[minIndex], sobases[k]) || sobases[minIndex] == sobases[k]
    {
      /* code modified by LLM (iteration 1): Fixed condition to properly compare elements for finding minimum */
      if !below(sobases[minIndex], sobases[j]) && sobases[minIndex] != sobases[j] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      sobases := Exchanger(sobases, i, minIndex);
    }
    i := i + 1;
  }
}