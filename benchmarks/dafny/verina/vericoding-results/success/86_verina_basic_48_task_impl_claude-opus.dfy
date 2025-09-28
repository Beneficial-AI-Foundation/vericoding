// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemma to prove 0 is a perfect square */
lemma ZeroIsPerfectSquare()
  ensures IsPerfectSquare(0)
{
  assert 0 * 0 == 0;
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed proof for n==0 case and strengthened loop invariants */
  if n == 0 {
    ZeroIsPerfectSquare();
    assert IsPerfectSquare(n as nat);
    result := true;
    return;
  }
  
  var i := 0;
  while i * i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> j * j < n
    invariant forall j :: 0 <= j < i ==> j * j != n
  {
    i := i + 1;
  }
  
  result := (i * i == n);
  
  if result {
    assert i * i == n;
    assert IsPerfectSquare(n as nat);
  } else {
    assert i * i > n;
    assert forall j :: 0 <= j < i ==> j * j != n;
    
    forall j | 0 <= j
      ensures j * j != n
    {
      if j < i {
        assert j * j != n;
      } else if j == i {
        assert j * j > n;
      } else {
        assert j > i;
        assert j * j >= i * i > n;
      }
    }
    assert !IsPerfectSquare(n as nat);
  }
}
// </vc-code>
