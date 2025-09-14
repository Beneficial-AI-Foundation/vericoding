

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LinearSearch(a: array<int>, e: int) returns (n:int)
  requires exists i::0<=i<a.Length && a[i]==e
  ensures 0<=n<a.Length && a[n]==e
  ensures forall k :: 0 <= k < n ==> a[k]!=e
// </vc-spec>
// <vc-code>
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] != e
        decreases a.Length - i
    {
        if a[i] == e {
            return i;
        }
        i := i + 1;
    }
    // This part of the code should be unreachable given the precondition
    // "exists i::0<=i<a.Length && a[i]==e"
    // However, Dafny requires all paths to return a value. 
    // In a real scenario, this would mean the precondition was violated.
    // We can use an assert false or a default return that satisfies static analysis,
    // although logically it won't be reached.
    // For verification purposes, we know 'e' must be found.
    assert false; // Or a panic mechanism if Dafny allowed it for unreachable code.
    return -1; // This line is just to appease the compiler, it won't be executed due to the loop invariant and precondition.
}
// </vc-code>

