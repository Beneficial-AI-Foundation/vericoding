// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified helper to just verify perfect square property */
lemma VerifyPerfectSquare(n: nat, i: nat)
  requires i * i == n
  ensures IsPerfectSquare(n)
{
  assert IsPerfectSquare(n);
}

lemma VerifyNotPerfectSquare(n: nat, i: nat)
  requires i * i < n < (i + 1) * (i + 1)
  ensures !IsPerfectSquare(n)
{
  forall j: nat ensures j * j != n {
    if j <= i {
      assert j * j <= i * i < n;
    } else {
      assert j >= i + 1;
      assert j * j >= (i + 1) * (i + 1) > n;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant by ensuring i*i <= n is maintained after increment */
{
  if n == 0 {
    result := true;
    VerifyPerfectSquare(0, 0);
    return;
  }
  
  var i := 0;
  while i * i < n && (i + 1) * (i + 1) <= n
    invariant i >= 0
    invariant i * i <= n
    invariant forall j: nat :: j < i ==> j * j < n
  {
    i := i + 1;
  }
  
  if i * i == n {
    result := true;
    VerifyPerfectSquare(n as nat, i as nat);
  } else {
    result := false;
    assert i * i < n;
    assert (i + 1) * (i + 1) > n;
    VerifyNotPerfectSquare(n as nat, i as nat);
  }
}
// </vc-code>
