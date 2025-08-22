//IMPL 
method only_once<T(==)>(a: array<T>, key: T) returns (b:bool)
  ensures (multiset(a[..])[key] ==1 ) <==> b
{
  var count := 0;
  var i := 0;
  
  /* code modified by LLM (iteration 1): Added proper loop invariant to track count relationship with multiset */
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant count == multiset(a[0..i])[key]
  {
    if a[i] == key {
      count := count + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to help verification connect loop result to postcondition */
  assert i == a.Length;
  assert a[0..i] == a[..];
  assert count == multiset(a[..])[key];
  
  b := count == 1;
}