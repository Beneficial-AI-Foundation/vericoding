// ATOM 
lemma BinarySearch(intSeq:seq<int>, key:int) returns (r:int)
    // original
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key
{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            return mid;
        }
    }
    return -1;
}

// ATOM 
predicate BinarySearchTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)
}

// ATOM 
lemma BinarySearchDeterministic(intSeq:seq<int>, key:int) returns (r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result

{  
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    /* code modified by LLM (iteration 1): Added proper invariants to prove deterministic binary search properties */
    while lo < hi
        invariant 0 <= lo <= hi <= |intSeq|
        invariant forall i:nat | i < lo :: intSeq[i] < key
        invariant forall i:nat | hi <= i < |intSeq| :: intSeq[i] >= key
        invariant hi < |intSeq| ==> intSeq[hi] >= key
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            /* code modified by LLM (iteration 1): Simplified the logic to find first occurrence when key is found */
            // Found the key, now find the first occurrence
            hi := mid;
        }
    }
    /* code modified by LLM (iteration 1): Added proper return logic to handle both found and not found cases */
    if lo < |intSeq| && intSeq[lo] == key {
        return lo;
    } else {
        return -1;
    }
}

// ATOM 
predicate BinarySearchDeterministicTransition(intSeq:seq<int>, key:int, r:int)
    requires (forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j])
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | i < |intSeq| :: intSeq[i] != key)

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

// ATOM 
lemma BinarySearchWrong1(intSeq:seq<int>, key:int) returns (r:int)
    // first element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key // i >= 0

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result
{
    if |intSeq| > 0 && intSeq[0] == key {
        return 0;
    }
    return -1;
}

// ATOM 
predicate BinarySearchWrong1Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 < i < |intSeq| :: intSeq[i] != key) // i >= 0

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

// ATOM 
lemma BinarySearchWrong2(intSeq:seq<int>, key:int) returns (r:int)
    // last element
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r >= 0 ==> r < |intSeq| && intSeq[r] == key
    ensures r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key // i < |intSeq|

    // make it deterministic
    ensures r < 0 ==> r == -1 // return -1 if not found
    ensures r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key // multiple matches return the first result
{
    if |intSeq| > 0 && intSeq[|intSeq|-1] == key {
        return |intSeq|-1;
    }
    return -1;
}

// ATOM 
predicate BinarySearchWrong2Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    && (r >= 0 ==> r < |intSeq| && intSeq[r] == key)
    && (r < 0 ==> forall i:nat | 0 <= i < |intSeq| - 1 :: intSeq[i] != key) // i < |intSeq|

    // make it deterministic
    && (r < 0 ==> r == -1) // return -1 if not found
    && (r >= 0 ==> forall i:nat | i < r :: intSeq[i] < key)
}

// ATOM 
lemma BinarySearchWrong3(intSeq:seq<int>, key:int) returns (r:int)
    // weaker spec
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures r < 0 || (r < |intSeq| && intSeq[r] == key) // post condition not correctly formed
{
    return -1;
}

// ATOM 
predicate BinarySearchWrong3Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    r < 0 || (r < |intSeq| && intSeq[r] == key)
}

// ATOM 
lemma BinarySearchWrong4(intSeq:seq<int>, key:int) returns (r:int)
    // non-realistic
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
    ensures 0 <= r < |intSeq| && intSeq[r] == key
{
    var lo:nat := 0;
    var hi:nat := |intSeq|;
    while lo < hi
    {
        var mid := (lo + hi) / 2;
        if (intSeq[mid] < key) {
            lo := mid + 1;
        } else if (intSeq[mid] > key) {
            hi := mid;
        } else {
            return mid;
        }
    }
    // This should never be reached due to the postcondition requirement
    return 0;
}

// ATOM 
predicate BinarySearchWrong4Transition(intSeq:seq<int>, key:int, r:int)
    requires forall i,j | 0 <= i <= j < |intSeq| :: intSeq[i] <= intSeq[j]
{
    0 <= r < |intSeq| && intSeq[r] == key
}