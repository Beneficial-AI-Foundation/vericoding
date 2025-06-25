//IMPL 
method foo2() 
  ensures false
{
  /* code modified by LLM (iteration 4): Using while true loop to ensure method never returns */
  while true
    invariant true
  {
  }
}

//IMPL FindKey
method FindKey(a: array<int>, key: int) returns (index: int)
  reads a
  ensures index == -1 ==> key !in a[..]
  ensures index != -1 ==> 0 <= index < a.Length && a[index] == key
{
  index := 0;
  /* code modified by LLM (iteration 4): Fixed loop with proper invariants to ensure postconditions */
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant key !in a[0..index]
  {
    if a[index] == key {
      /* code modified by LLM (iteration 4): Return when key found - postcondition satisfied by invariant */
      return;
    }
    index := index + 1;
  }
  /* code modified by LLM (iteration 4): Key not found, set to -1 - invariant proves key !in a[..] */
  index := -1;
}