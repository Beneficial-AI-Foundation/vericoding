// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is


predicate IsSorted( s: seq<int> )
{
    forall p,q | 0<=p<q<|s| :: s[p]<=s[q]
}

// <vc-helpers>
lemma InsertLemma(arr: seq<int>, i: int, j: int, elem: int, arr2: seq<int>)
    requires 0 <= i < j <= |arr|
    requires |arr2| == |arr|
    requires arr[0..i] == arr2[0..i]
    requires arr2[i..j-1] == arr[i+1..j]
    requires arr2[j-1] == elem
    requires arr2[j..] == arr[j..]
    ensures multiset(arr2) == multiset(arr)
{
    // Calculate the multiset equality by considering the different parts
    assert multiset(arr) == multiset(arr[0..i]) + multiset(arr[i..j]) + multiset(arr[j..]);
    assert multiset(arr2) == multiset(arr2[0..i]) + multiset(arr2[i..j]) + multiset(arr2[j..]);
    
    // The parts before i and after j are the same
    assert multiset(arr[0..i]) == multiset(arr2[0..i]);
    assert multiset(arr[j..]) == multiset(arr2[j..]);
    
    // The middle parts: arr[i..j] vs arr2[i..j]
    // Note: arr[i..j] = [arr[i]] + arr[i+1..j]
    // And arr2[i..j] = arr[i+1..j] + [elem] 
    assert arr[i..j] == [arr[i]] + arr[i+1..j];
    assert multiset(arr2[i..j]) == multiset(arr[i+1..j]) + multiset([elem]);
    
    // Since arr2[j-1] == elem and arr[i] == elem (by assumption in the calling context)
    // We actually need to show multiset([arr[i]] + arr[i+1..j]) == multiset(arr[i+1..j] + [elem])
    // This requires that elem == arr[i]
    assert [arr[i]] + arr[i+1..j] == [elem] + arr[i+1..j];
    assert multiset([arr[i]] + arr[i+1..j]) == multiset([elem] + arr[i+1..j]);
}

lemma InsertSortedLemma(sorted: seq<int>, elem: int, pos: int)
    requires IsSorted(sorted)
    requires 0 <= pos <= |sorted|
    requires (pos == 0 || sorted[pos-1] <= elem)
    requires (pos < |sorted| ==> elem <= sorted[pos])
    ensures IsSorted(sorted[0..pos] + [elem] + sorted[pos..])
{
    var newSeq := sorted[0..pos] + [elem] + sorted[pos..];
    
    // Check all pairs in the new sequence
    forall p, q | 0 <= p < q < |newSeq|
        ensures newSeq[p] <= newSeq[q]
    {
        if q < pos {
            // Both elements are in the original sorted[0..pos]
            assert newSeq[p] == sorted[p];
            assert newSeq[q] == sorted[q];
            assert sorted[p] <= sorted[q];
        } 
        else if p >= pos {
            // Both elements are in the original sorted[pos..]
            assert newSeq[p] == (if p == pos then elem else sorted[p-1]);
            assert newSeq[q] == (if q == pos then elem else sorted[q-1]);
            if p == pos {
                assert newSeq[p] == elem;
                if q == pos + 1 {
                    assert newSeq[q] == sorted[pos];
                    assert elem <= sorted[pos];
                } else {
                    assert newSeq[q] == sorted[q-1];
                    assert sorted[pos] <= sorted[q-1];
                }
            } else {
                assert newSeq[p] == sorted[p-1];
                if q == pos {
                    assert newSeq[q] == elem;
                    assert sorted[p-1] <= sorted[pos] <= elem;
                } else {
                    assert newSeq[q] == sorted[q-1];
                    assert sorted[p-1] <= sorted[q-1];
                }
            }
        }
        else {
            // p is in first part, q is at pos or after
            if q == pos {
                // q is the inserted element
                assert newSeq[q] == elem;
                assert newSeq[p] == sorted[p];
                if p == pos-1 {
                    assert sorted[pos-1] <= elem;
                } else {
                    assert sorted[p] <= sorted[pos-1] <= elem;
                }
            } 
            else {
                // q > pos, so newSeq[q] = sorted[q-1]
                assert newSeq[q] == sorted[q-1];
                if p == pos-1 {
                    // Last element of first part and first element of second part
                    assert newSeq[p] == sorted[pos-1];
                    assert sorted[pos-1] <= elem <= sorted[pos] <= sorted[q-1];
                } 
                else {
                    // p < pos-1
                    assert newSeq[p] == sorted[p];
                    assert sorted[p] <= sorted[pos-1] <= elem <= sorted[pos] <= sorted[q-1];
                }
            }
        }
    }
}

lemma MultisetLemma(s: seq<int>, r: seq<int>, arr: seq<int>, i: int)
    requires 0 <= i <= |arr|
    requires multiset(r) + multiset(arr[i..]) == multiset(s)
    requires |arr| > 0
    ensures multiset(r) + multiset(arr[i..]) == multiset(s)
{
}
// </vc-helpers>

// <vc-spec>
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
// </vc-spec>
// <vc-code>
{
  var arr := s;
  var i := 0;
  r := [];
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |r| == i
    invariant multiset(r) + multiset(arr[i..]) == multiset(s)
    invariant IsSorted(r)
  {
    var elem := arr[i];
    var j := 0;
    while j < |r| && r[j] < elem
      invariant 0 <= j <= |r|
      invariant forall k | 0 <= k < j :: r[k] < elem
    {
      j := j + 1;
    }
    
    var new_r := r[0..j] + [elem] + r[j..];
    
    // Update multiset invariant
    assert multiset(new_r) == multiset(r) + multiset([elem]);
    assert multiset(arr[i..]) == multiset([elem]) + multiset(arr[i+1..]);
    assert multiset(new_r) + multiset(arr[i+1..]) == multiset(r) + multiset(arr[i..]);
    
    // Update sortedness
    if |r| > 0 {
        InsertSortedLemma(r, elem, j);
    } else {
        assert IsSorted([elem]);
    }
    
    r := new_r;
    i := i + 1;
  }
}
// </vc-code>

