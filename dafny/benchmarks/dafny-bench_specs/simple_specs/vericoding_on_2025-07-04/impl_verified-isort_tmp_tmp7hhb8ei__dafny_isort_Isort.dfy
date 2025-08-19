//ATOM
// Dafny is designed to be familiar to those programming in an OOP language like
// Java, so, we have plain old ordinary mutable arrays rather than the functional
// list data structures that we saw in Coq. This means that unlike our Coq
// and Python examples, we can sort our array in-place and avoid needing a whole
// bunch of intermediary allocations.

// Just as before, we need a way of defining what it means for an array of nats
// to be sorted:
predicate sorted(a: seq<nat>)
{
  true // TODO
}

//IMPL 
method Isort(a: array<nat>)
  modifies a
  ensures sorted(a[..])
{
  // Since sorted(a) is defined as true, any implementation will satisfy the postcondition
  // We can implement insertion sort for completeness
  var i := 1;
  while i < a.Length
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    i := i + 1;
  }
}