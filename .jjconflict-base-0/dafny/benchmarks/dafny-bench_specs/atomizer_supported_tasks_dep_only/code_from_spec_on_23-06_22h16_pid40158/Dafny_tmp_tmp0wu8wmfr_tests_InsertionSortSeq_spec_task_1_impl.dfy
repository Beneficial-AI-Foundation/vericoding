// Insertion sort.
//
// Author: Snorri Agnarsson, snorri@hi.is

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
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := s;
    var i := 1;
    
    while i < |r|
        invariant 0 <= i <= |r|
        invariant multiset(r) == multiset(s)
        invariant IsSorted(r[..i])
    {
        var key := r[i];
        var j := i - 1;
        
        /* code modified by LLM (iteration 1): Fixed the inner loop with correct invariants */
        while j >= 0 && r[j] > key
            invariant -1 <= j < i
            invariant multiset(r) == multiset(s)
            invariant forall k | j < k < i :: r[k] > key
            invariant j >= 0 ==> IsSorted(r[..j+1])
            invariant IsSorted(r[i+1..])
            invariant forall k1, k2 | 0 <= k1 <= j && i+1 <= k2 < |r| :: r[k1] <= r[k2]
            invariant forall k1, k2 | 0 <= k1 <= j && j+1 < k2 < i :: r[k1] <= key
        {
            r := r[j+1 := r[j]];
            j := j - 1;
        }
        
        r := r[j+1 := key];
        
        /* code modified by LLM (iteration 1): Added helper assertions to prove sortedness */
        assert j+1 <= i;
        assert forall k | 0 <= k <= j :: r[k] <= key;
        assert forall k | j+2 <= k <= i :: r[k] >= key;
        
        /* code modified by LLM (iteration 1): Prove IsSorted(r[..i+1]) step by step */
        assert forall p, q | 0 <= p < q <= j :: r[p] <= r[q];
        assert forall p | 0 <= p <= j :: r[p] <= r[j+1];
        assert forall q | j+2 <= q <= i :: r[j+1] <= r[q];
        assert forall p, q | j+2 <= p < q <= i :: r[p] <= r[q];
        
        /* code modified by LLM (iteration 1): Final assertion for the combined sorted property */
        assert forall p, q | 0 <= p < q <= i :: r[p] <= r[q];
        assert IsSorted(r[..i+1]);
        
        i := i + 1;
    }
}