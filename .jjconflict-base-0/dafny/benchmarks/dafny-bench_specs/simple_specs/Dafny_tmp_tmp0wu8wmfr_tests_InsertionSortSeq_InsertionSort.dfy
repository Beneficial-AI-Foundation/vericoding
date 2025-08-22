//ATOM
// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
  forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}


// SPEC

method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
{
}
