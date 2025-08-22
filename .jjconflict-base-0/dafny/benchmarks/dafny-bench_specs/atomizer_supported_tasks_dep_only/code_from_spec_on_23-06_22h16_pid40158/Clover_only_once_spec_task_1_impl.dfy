//IMPL 
method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{
  var count := 0;
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count == multiset(a[0..i])[key]
  {
    if a[i] == key {
      count := count + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion to help Dafny prove equivalence of array slices */
  assert a[0..a.Length] == a[..];
  
  b := count == 1;
}