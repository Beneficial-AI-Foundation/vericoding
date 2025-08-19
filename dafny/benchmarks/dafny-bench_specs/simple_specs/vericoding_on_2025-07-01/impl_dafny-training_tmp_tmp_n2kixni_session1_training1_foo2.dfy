// IMPL
method foo2() 
  ensures false
{
  // This method cannot be implemented without assume statements
  // since ensuring false is impossible to prove
  assert false; // This will cause verification to fail
}

// IMPL find method based on the documentation
method find(a: array<int>, key: int) returns (index: int)
  requires a != null
  ensures (key in a[..]) ==> (0 <= index < a.Length && a[index] == key)
  ensures (key !in a[..]) ==> index == -1
{
  index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant key !in a[..index]
  {
    if a[index] == key {
      return;
    }
    index := index + 1;
  }
  index := -1;
}