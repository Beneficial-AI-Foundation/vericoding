// Noa Leron 207131871
// Tsuri Farhana 315016907



predicate Sorted(q: seq<int>) {
    forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/*
Goal: Implement the well known merge sort algorithm in O(a.Length X log_2(a.Length)) time, recursively.

- Divide the contents of the original array into two local arrays
- After sorting the local arrays (recursively), merge the contents of the two returned arrays using the Merge method (see below)
- DO NOT modify the specification or any other part of the method's signature
- DO NOT introduce any further methods
*/

ghost predicate Inv(a: seq<int>, a1: seq<int>, a2: seq<int>, i: nat, mid: nat){
    (i <= |a1|) && (i <= |a2|) && (i+mid <= |a|) &&
    (a1[..i] == a[..i]) && (a2[..i] == a[mid..(i+mid)])
}

/*
Goal: Implement iteratively, correctly, efficiently, clearly

DO NOT modify the specification or any other part of the method's signature
*/
method Merge(b: array<int>, c: array<int>, d: array<int>)
    requires b != c && b != d && b.Length == c.Length + d.Length
    requires Sorted(c[..]) && Sorted(d[..])
    ensures Sorted(b[..]) && multiset(b[..]) == multiset(c[..])+multiset(d[..])
    modifies b
{
  assume{:axiom} false;
}


//This is a method that replace the loop body


//Loop invariant - b is sprted so far and the next two potential values that will go into b are bigger then the biggest value in b.
ghost predicate InvSorted(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    ((i+j > 0 && i < |c|) ==> (b[j + i - 1] <= c[i])) &&
    ((i+j > 0 && j < |d|) ==> (b[j + i - 1] <= d[j])) &&
    Sorted(b[..i+j])
    }


//Loop invariant - the multiset of the prefix of b so far is the same multiset as the prefixes of c and d so far.
ghost predicate InvSubSet(b: seq<int>, c: seq<int>, d: seq<int>, i: nat, j: nat){
    i <= |c| && j <= |d| && i + j <= |b| &&
    multiset(b[..i+j]) == multiset(c[..i]) + multiset(d[..j])
}

//This lemma helps dafny see that if the prefixs of arrays are the same multiset until the end of the arrays,
//all the arrays are the same multiset.


//This lemma helps dafny see that after adding the next value from c to b the prefixes are still the same subsets.

// <vc-helpers>
lemma SplitMultiset(a: seq<int>, mid: nat)
    requires mid <= |a|
    ensures multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..])
{
    if |a| == 0 {
        assert a[..] == [];
        assert a[..mid] == [];
        assert a[mid..] == [];
    } else if mid == 0 {
        assert a[..mid] == [];
        assert a[mid..] == a[..];
    } else if mid == |a| {
        assert a[..mid] == a[..];
        assert a[mid..] == [];
    } else {
        assert a[..] == a[..mid] + a[mid..];
    }
}
// </vc-helpers>

// <vc-spec>
method MergeSort(a: array<int>) returns (b: array<int>)
    ensures b.Length == a.Length && Sorted(b[..]) && multiset(a[..]) == multiset(b[..])
    decreases a.Length
// </vc-spec>
// <vc-code>
{
    if a.Length == 0 {
        b := new int[0];
        return;
    }
    
    if a.Length == 1 {
        b := new int[1];
        b[0] := a[0];
        return;
    }
    
    var mid := a.Length / 2;
    
    // Create left half array
    var left := new int[mid];
    var i := 0;
    while i < mid
        invariant 0 <= i <= mid
        invariant forall k :: 0 <= k < i ==> left[k] == a[k]
    {
        left[i] := a[i];
        i := i + 1;
    }
    assert forall k :: 0 <= k < mid ==> left[k] == a[k];
    
    // Create right half array
    var right := new int[a.Length - mid];
    i := 0;
    while i < a.Length - mid
        invariant 0 <= i <= a.Length - mid
        invariant forall k :: 0 <= k < i ==> right[k] == a[mid + k]
    {
        right[i] := a[mid + i];
        i := i + 1;
    }
    assert forall k :: 0 <= k < a.Length - mid ==> right[k] == a[mid + k];
    
    // Establish the equality of sequences
    assert left[..] == a[..mid];
    assert right[..] == a[mid..a.Length];
    
    // Prove multiset property for split
    SplitMultiset(a[..], mid);
    assert multiset(a[..]) == multiset(a[..mid]) + multiset(a[mid..a.Length]);
    assert multiset(left[..]) == multiset(a[..mid]);
    assert multiset(right[..]) == multiset(a[mid..a.Length]);
    assert multiset(a[..]) == multiset(left[..]) + multiset(right[..]);
    
    // Recursively sort both halves
    var sortedLeft := MergeSort(left);
    var sortedRight := MergeSort(right);
    
    assert multiset(sortedLeft[..]) == multiset(left[..]);
    assert multiset(sortedRight[..]) == multiset(right[..]);
    assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(left[..]) + multiset(right[..]);
    assert multiset(sortedLeft[..]) + multiset(sortedRight[..]) == multiset(a[..]);
    
    // Create result array and merge
    b := new int[a.Length];
    assert b.Length == sortedLeft.Length + sortedRight.Length;
    
    Merge(b, sortedLeft, sortedRight);
    
    // Verify final properties
    assert Sorted(b[..]);
    assert multiset(b[..]) == multiset(sortedLeft[..]) + multiset(sortedRight[..]);
    assert multiset(b[..]) == multiset(a[..]);
}
// </vc-code>

