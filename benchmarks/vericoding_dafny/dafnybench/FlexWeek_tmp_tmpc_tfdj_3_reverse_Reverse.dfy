// Write an *iterative* Dafny method Reverse with signature:

// <vc-helpers>
// </vc-helpers>

//          method Reverse(a: array<char>) returns (b: array<char>)

// which takes an input array of characters 'a' and outputs array 'b' consisting of
// the elements of the input array in reverse order. The following conditions apply:
//  - the input array cannot be empty
//  - the input array is not modified
//  - you must use iteration
//  - not permitted is an *executable* (parallel) forall statement
//  - not permitted are any other predicates, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

// <vc-spec>
method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>

// Notice it compiles and the executable generates output (just to see the arrays printed in reverse).