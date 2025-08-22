// Dafny is designed to be familiar to those programming in an OOP language like
// Java, so, we have plain old ordinary mutable arrays rather than the functional
// list data structures that we saw in Coq.  This means that unlike our Coq
// and Python examples, we can sort our array in-place and avoid needing a whole
// bunch of intermediary allocations.

// Just as before, we need a way of defining what it means for an array of nats
// to be sorted:
//ATOM 
predicate sorted(a: seq<nat>)
{
    true // TODO
}

//IMPL 
method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{
    /* code modified by LLM (iteration 4): Added proper sorted predicate implementation */
    predicate sortedSeq(s: seq<nat>) {
        forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    }
    
    /* code modified by LLM (iteration 4): Complete rewrite of insertion sort with proper invariants */
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant sortedSeq(a[..i])
    {
        var key := a[i];
        var j := i - 1;
        
        while j >= 0 && a[j] > key
            invariant -1 <= j < i
            invariant sortedSeq(a[..j+1])
            invariant forall k :: j+1 < k < i ==> a[k] > key
            invariant forall k :: j+1 < k < i ==> a[k] <= a[k+1]
            invariant a[i] == key
        {
            a[j + 1] := a[j];
            j := j - 1;
        }
        
        a[j + 1] := key;
        
        /* code modified by LLM (iteration 4): Added assertion to help verification */
        assert sortedSeq(a[..i+1]);
        
        i := i + 1;
    }
    
    /* code modified by LLM (iteration 4): Final assertion to establish postcondition */
    assert sortedSeq(a[..]);
    assert sorted(a[..]);  // This follows from the atom definition
}