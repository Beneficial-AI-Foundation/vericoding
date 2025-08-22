//IMPL
method IsPerfectSquare(n: int) returns (result: bool)
  requires n >= 0
  ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
  ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
  if n == 0 {
    result := true;
    return;
  }
  
  var i := 1;
  /* code modified by LLM (iteration 1): strengthened loop invariant to track that no perfect square has been found so far and added upper bound reasoning */
  while i * i <= n
    invariant 1 <= i
    invariant forall j: int :: 0 <= j < i ==> j * j != n
    invariant forall j: int :: 0 <= j < i ==> j * j < n
    invariant i * i > n ==> forall k: int :: k * k == n ==> k < i
  {
    if i * i == n {
      result := true;
      return;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added assertion to help prove the postcondition */
  assert i * i > n;
  assert forall j: int :: 0 <= j < i ==> j * j != n;
  assert forall k: int :: k >= i ==> k * k >= i * i > n;
  
  result := false;
}