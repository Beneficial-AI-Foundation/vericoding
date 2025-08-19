// IMPL
method IsPerfectSquare(n: int) returns (result: bool)
  requires n >= 0
  ensures result == true ==> (exists i: int :: 0 <= i <= n && i * i == n)
  ensures result == false ==> (forall a: int :: 0 < a*a < n ==> a*a != n)
{
  if n == 0 {
    result := true;
    /* code modified by LLM (iteration 2): added assertion to help prove postcondition for n=0 case */
    assert 0 * 0 == 0;
  } else {
    var i := 0;
    /* code modified by LLM (iteration 2): fixed loop condition and invariants to prevent overflow */
    while i * i < n && (i + 1) * (i + 1) <= n
      invariant 0 <= i
      invariant i * i <= n
      invariant forall j: int :: 0 <= j < i ==> j * j < n
    {
      i := i + 1;
    }
    
    if i * i == n {
      /* code modified by LLM (iteration 2): added assertion to establish witness for existential */
      assert i * i == n && 0 <= i <= n;
      result := true;
    } else {
      result := false;
    }
  }
}