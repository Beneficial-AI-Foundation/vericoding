// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found.

// Simple test cases to check the post-condition.

/*
a) Identify adequate pre and post-conditions for this method, 
and encode them as “requires” and “ensures” clauses in Dafny. 
You can use the predicate below if needed.

b) Identify an adequate loop variant and loop invariant, and encode them 
as “decreases” and “invariant” clauses in Dafny.
*/

// <vc-helpers>
predicate InArray<T(==)>(x: T, a: array<T>)
  reads a
{
  exists i :: 0 <= i < a.Length && a[i] == x
}

predicate NotInArray<T(==)>(x: T, a: array<T>)
  reads a
{
  forall i :: 0 <= i < a.Length ==> a[i] != x
}
// </vc-helpers>

// <vc-spec>
method binarySearch(a: array<int>, x: int) returns (index: int) 
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x 
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// <vc-code>
{
    var low := 0;
    var high := a.Length;

    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant isSorted(a)
        invariant forall i :: 0 <= i < low ==> a[i] != x
        invariant forall i :: high <= i < a.Length ==> a[i] != x
        invariant (exists i_x :: low <= i_x < high && a[i_x] == x) ==> (exists i_in_a :: 0 <= i_in_a < a.Length && a[i_in_a] == x) // If x is in current search range, it must be in the original array
        invariant (forall i_x :: low <= i_x < high ==> a[i_x] != x) ==> (forall i_in_a :: 0 <= i_in_a < a.Length ==> a[i_in_a] != x || i_in_a < low || i_in_a >= high)
        decreases high - low
    {
        var mid := low + (high - low) / 2;
        if a[mid] == x {
            return mid;
        } else if a[mid] < x {
            low := mid + 1;
        } else { // a[mid] > x
            high := mid;
        }
    }
    return -1;
}
// </vc-code>

