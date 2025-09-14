

// <vc-helpers>
lemma lemma_exists_implies_element_found(s: seq<int>, element: int, pos: int)
  requires pos >= 1
  requires exists i :: 0 <= i < |s| && s[i] == element
  ensures exists i :: 0 <= i < |s| && s[i] == element
{
}
// </vc-helpers>

// <vc-spec>
method FindPositionOfElement(a:array<int>,Element:nat,n1:nat,s1:seq<int>) returns (Position:int,Count:nat)
        requires n1 == |s1| && 0 <= n1 <= a.Length
        requires forall i:: 0<= i < |s1| ==> a[i] == s1[i]
        ensures Position == -1 || Position >= 1
        ensures |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
// </vc-spec>
// <vc-code>
{
    var position := -1;
    var count := 0;

    if n1 > 0 { // Add this check to prevent loop from running with n1-1 < 0
        for i := 0 to n1-1
            invariant 0 <= i <= n1
            invariant position == -1 || (0 <= position - 1 < i && a[position-1] == Element)
            invariant count == (if position == -1 then 0 else 1)
            invariant forall k :: 0 <= k < i && a[k] != Element ==> position == -1
        {
            if a[i] == Element {
                position := i + 1; // Position is 1-indexed
                count := 1;
                break;
            }
        }
    }
    
    // Post-loop invariants
    // If position is found, it's 1-indexed and a[position-1] == Element
    // If position is -1, element was not found in the loop
    
    // Ensure 1: Position == -1 || Position >= 1
    // This is already true by construction: position is either -1 or i+1 for some i >= 0.

    // Ensure 2: |s1| != 0 && Position >= 1 ==> exists i:: 0 <= i < |s1| && s1[i] == Element
    if n1 != 0 && position >= 1 {
        // If position >= 1, it means we found the element.
        // position stores i+1 from the loop, so a[position-1] == Element.
        // Since a[j] == s1[j] for all j, it means s1[position-1] == Element.
        // And 0 <= position-1 < n1 is true because position <= n1 (max i+1 is (n1-1)+1 = n1).
        assert 0 <= position - 1 < n1;
        assert a[position-1] == Element;
        assert s1[position-1] == Element;
        assert (exists k :: 0 <= k < |s1| && s1[k] == Element); // Add this assertion
        lemma_exists_implies_element_found(s1, Element, position);
    }
    
    // If position is -1, then the element was not found.
    // If n1 == 0, then trivially position is -1.
    // Otherwise, if position is -1 and n1 > 0, then the element was not present in the array.
    
    Position := position;
    Count := count;
}
// </vc-code>

