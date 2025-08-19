predicate sorted(a: seq<nat>)
{
  true // TODO
}

//IMPL 
method Isort(a: array<nat>)
  modifies a
  ensures sorted(a[..])
{
  /* code modified by LLM (iteration 2): fixed loop invariants to properly handle array element shifting */
  if a.Length <= 1 {
    return;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant sorted(a[0..i])
  {
    var key := a[i];
    var j := i - 1;
    /* code modified by LLM (iteration 2): store original array state for this iteration */
    ghost var orig := a[..];
    
    /* code modified by LLM (iteration 2): updated invariants to use orig state instead of old() */
    while j >= 0 && a[j] > key
      invariant -1 <= j < i
      invariant forall k :: j + 2 <= k <= i ==> a[k] > key
      invariant forall k :: j + 2 <= k <= i ==> a[k] == orig[k-1]
      invariant forall k :: 0 <= k <= j ==> a[k] == orig[k]
      invariant forall k :: i + 1 <= k < a.Length ==> a[k] == orig[k]
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    i := i + 1;
  }
}