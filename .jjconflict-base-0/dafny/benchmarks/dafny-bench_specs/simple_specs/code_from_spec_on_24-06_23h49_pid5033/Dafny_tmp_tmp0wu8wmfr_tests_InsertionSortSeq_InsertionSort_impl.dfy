//ATOM
// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

predicate IsSorted( s: seq<int> )
{
  forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

//IMPL InsertionSort
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
      invariant forall k | 0 <= k < j :: r[k] <= x
    {
      j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): Added assertions to help verification */
    assert 0 <= j <= |r|;
    assert forall k | 0 <= k < j :: r[k] <= x;
    assert j == |r| || r[j] > x;
    
    /* code modified by LLM (iteration 1): Call helper lemma to prove insertion correctness */
    InsertionPreservesOrder(r, x, j);
    
    r := r[..j] + [x] + r[j..];
  }
}

/* code modified by LLM (iteration 1): Added helper lemma to prove insertion maintains sorted order and multiset equality */
lemma InsertionPreservesOrder(r: seq<int>, x: int, j: int)
  requires 0 <= j <= |r|
  requires IsSorted(r)
  requires forall k | 0 <= k < j :: r[k] <= x
  requires j == |r| || r[j] > x
  ensures IsSorted(r[..j] + [x] + r[j..])
  ensures multiset(r[..j] + [x] + r[j..]) == multiset(r) + multiset([x])
{
  var new_r := r[..j] + [x] + r[j..];
  
  /* code modified by LLM (iteration 1): Prove multiset equality step by step */
  assert r[..j] + r[j..] == r;
  assert multiset(r[..j] + r[j..]) == multiset(r);
  assert multiset(new_r) == multiset(r[..j]) + multiset([x]) + multiset(r[j..]);
  assert multiset(r[..j]) + multiset(r[j..]) == multiset(r);
  assert multiset(new_r) == multiset(r) + multiset([x]);
  
  /* code modified by LLM (iteration 1): Prove sorted property by cases */
  forall p, q | 0 <= p < q < |new_r|
    ensures new_r[p] <= new_r[q]
  {
    /* code modified by LLM (iteration 1): Handle all cases of element positions */
    if p < j && q < j {
      // Both elements are in the prefix r[..j]
      assert new_r[p] == r[p];
      assert new_r[q] == r[q];
      assert r[p] <= r[q]; // from IsSorted(r)
    } else if p < j && q == j {
      // First element in prefix, second is the inserted element
      assert new_r[p] == r[p];
      assert new_r[q] == x;
      assert r[p] <= x; // from precondition
    } else if p == j && q > j {
      // First is inserted element, second is in suffix
      assert new_r[p] == x;
      assert new_r[q] == r[q-1];
      if j < |r| {
        assert r[j] > x; // from precondition
        assert x <= r[j]; // contradiction resolved by j == |r| case
      }
      assert q-1 >= j;
      if j < |r| {
        assert r[j] > x;
        assert r[j] <= r[q-1]; // from IsSorted(r)
        assert x < r[j] <= r[q-1];
      }
    } else if p < j && q > j {
      // First in prefix, second in suffix  
      assert new_r[p] == r[p];
      assert new_r[q] == r[q-1];
      assert r[p] <= x; // from precondition
      if j < |r| {
        assert r[j] > x;
        assert r[j] <= r[q-1]; // from IsSorted(r)
        assert r[p] <= x < r[j] <= r[q-1];
      } else {
        // j == |r|, so q-1 >= j-1 and we need r[p] <= r[q-1]
        assert q-1 >= j-1;
        if q-1 >= j && j > 0 {
          assert r[p] <= r[q-1]; // from IsSorted(r)
        } else if j == 0 {
          // This case shouldn't happen given our constraints
          assert false;
        }
      }
    } else {
      // Both elements are in the suffix r[j..]
      assert p > j && q > j;
      assert new_r[p] == r[p-1];
      assert new_r[q] == r[q-1];
      assert p-1 >= j && q-1 >= j;
      assert p-1 < q-1;
      assert r[p-1] <= r[q-1]; // from IsSorted(r)
    }
  }
}