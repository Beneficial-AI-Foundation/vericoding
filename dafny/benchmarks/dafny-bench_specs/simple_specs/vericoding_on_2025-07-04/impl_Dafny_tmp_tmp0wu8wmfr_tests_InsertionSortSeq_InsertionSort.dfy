//ATOM
// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
  forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

//IMPL 
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
  ensures multiset(r) == multiset(s)
  ensures IsSorted(r)
{
  r := [];
  
  for i := 0 to |s|
    invariant multiset(r) == multiset(s[..i])
    invariant IsSorted(r)
  {
    var x := s[i];
    var j := 0;
    
    while j < |r| && r[j] <= x
      invariant 0 <= j <= |r|
      /* code modified by LLM (iteration 4): added invariant to ensure all elements before j are <= x */
      invariant forall k | 0 <= k < j :: r[k] <= x
    {
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 4): store old r for reasoning about sortedness */
    var old_r := r;
    r := r[..j] + [x] + r[j..];
    
    /* code modified by LLM (iteration 4): key assertions about the structure after insertion */
    assert forall k | 0 <= k < j :: r[k] <= x;
    assert j == |old_r| || old_r[j] > x;
    assert forall k | j < k < |old_r| :: old_r[k] > x;
    
    /* code modified by LLM (iteration 4): prove elements in right part are correctly positioned */
    assert forall k | j + 1 <= k < |r| :: r[k] == old_r[k-1];
    assert forall k | j + 1 <= k < |r| :: r[k] > x;
    
    /* code modified by LLM (iteration 4): prove sortedness is maintained by systematic case analysis */
    // Left part (before insertion point) remains sorted
    assert forall p, q | 0 <= p < q < j :: r[p] <= r[q];
    
    // Right part (after insertion point) remains sorted
    assert forall p, q | j + 1 <= p < q < |r| :: r[p] <= r[q];
    
    // Left part to inserted element
    assert forall p | 0 <= p < j :: r[p] <= r[j];
    
    // Inserted element to right part
    assert forall q | j < q < |r| :: r[j] <= r[q];
    
    // Left part to right part (transitivity through inserted element)
    assert forall p, q | 0 <= p < j && j < q < |r| :: r[p] <= r[j] <= r[q];
  }
}