// <vc-preamble>
/*
 * numpy.searchsorted: Find indices where elements should be inserted to maintain order.
 * 
 * Given a sorted array and values, returns indices such that inserting each element
 * at the corresponding index would preserve the sorted order. Implements 'left' side
 * behavior returning the leftmost suitable insertion position.
 */
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method numpy_searchsorted(a: seq<real>, v: seq<real>) returns (indices: seq<nat>)
    // Precondition: input array must be sorted in ascending order
    requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
    
    // Postcondition: return sequence has same length as input values
    ensures |indices| == |v|
    
    // Postcondition: all returned indices are valid insertion points
    ensures forall k :: 0 <= k < |indices| ==> 0 <= indices[k] <= |a|
    
    // Postcondition: left insertion property - all elements before idx are strictly less
    ensures forall k :: 0 <= k < |indices| ==>
        forall i :: 0 <= i < indices[k] ==> a[i] < v[k]
    
    // Postcondition: sorted property - all elements at or after idx are greater than or equal
    ensures forall k :: 0 <= k < |indices| ==>
        forall j :: indices[k] <= j < |a| ==> v[k] <= a[j]
    
    // Postcondition: leftmost property - idx is the leftmost valid insertion point
    ensures {:nowarn} forall k :: 0 <= k < |indices| ==>
        forall pos {:trigger pos} :: 0 <= pos < indices[k] ==>
            exists i :: pos <= i < |a| && a[i] >= v[k]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
