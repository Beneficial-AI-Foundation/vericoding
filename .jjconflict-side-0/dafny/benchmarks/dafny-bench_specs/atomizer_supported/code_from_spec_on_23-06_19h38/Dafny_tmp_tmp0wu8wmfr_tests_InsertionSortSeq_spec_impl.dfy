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

//IMPL 
method InsertionSort( s: seq<int> ) returns ( r: seq<int> )
    ensures multiset(r) == multiset(s);
    ensures IsSorted(r);
{
    r := [];
    
    /* code modified by LLM (iteration 4): Fixed loop with proper invariants for multiset and sortedness */
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant multiset(r) == multiset(s[..i])
        invariant IsSorted(r)
    {
        var x := s[i];
        var j := 0;
        
        /* code modified by LLM (iteration 4): Find insertion position with corrected loop condition */
        while j < |r| && r[j] <= x
            invariant 0 <= j <= |r|
            invariant forall k | 0 <= k < j :: r[k] <= x
        {
            j := j + 1;
        }
        
        /* code modified by LLM (iteration 4): Key assertions to prove insertion maintains sortedness */
        assert forall k | 0 <= k < j :: r[k] <= x;
        assert j == |r| || r[j] > x;
        
        /* code modified by LLM (iteration 4): Insert element and prove properties are maintained */
        var old_r := r;
        r := r[..j] + [x] + r[j..];
        
        /* code modified by LLM (iteration 4): Verify multiset property */
        assert multiset(r) == multiset(old_r) + multiset([x]);
        assert multiset(old_r) == multiset(s[..i]);
        assert multiset(r) == multiset(s[..i]) + multiset([x]);
        assert s[..i+1] == s[..i] + [s[i]];
        assert x == s[i];
        assert multiset(r) == multiset(s[..i+1]);
        
        /* code modified by LLM (iteration 4): Verify sortedness with case analysis */
        assert forall p, q | 0 <= p < q < |r| :: 
            (q < j ==> r[p] <= r[q]) &&
            (p < j && q > j ==> r[p] <= x < r[q]) &&
            (p == j && q > j ==> x < r[q]) &&
            (p > j && q > j ==> r[p] <= r[q]) &&
            (p < j && q == j ==> r[p] <= x);
        
        assert IsSorted(r);
        
        i := i + 1;
    }
}