//ATOM
// Write an *iterative* Dafny method Reverse with signature:
//     method Reverse(a: array<char>) returns (b: array<char>)

// which takes an input array of characters 'a' and outputs array 'b' consisting of
// the elements of the input array in reverse order. The following conditions apply:
// - the input array cannot be empty
// - the input array is not modified
// - you must use iteration
// - not permitted is an *executable* (parallel) forall statement
// - not permitted are any other predicates, functions or methods

// For the purposes of this practice exercise, I'll include a test method.

method Reverse(a: array<char>) returns (b: array<char>)
requires a.Length > 0
ensures a.Length == b.Length
ensures forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k]
{
  b := [];
  assume a.Length ==> b.Length;
  assume forall k :: 0 <= k < a.Length ==> b[k] == a[(a.Length-1) - k];
  return b;
}


// SPEC



method Main()
{
 var a := new char[8];
 a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7] := 'd', 'e', 's', 'r', 'e', 'v', 'e', 'r';
 var b := Reverse(a);
 print b[..];

 a := new char[1];
 a[0] := '!';
 b := Reverse(a);
 print b[..], '\n';
}
