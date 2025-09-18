// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): no-op helper retained for verification */
lemma NoOpHelper() ensures true {
}

// </vc-helpers>

// <vc-spec>
method IsPerfectSquareFn(n: int) returns (result: bool)
    requires n >= 0
    ensures result <==> IsPerfectSquare(n as nat)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use nat indices, loop up to N with proper decreases and break on match */
  var N := n as nat;
  var i: nat := 0;
  var w: nat := 0;
  result := false;
  while i <= N
    decreases (N + 1) - i
    invariant 0 <= i <= N + 1
    invariant forall j: nat :: j < i ==> j * j != N
  {
    if i * i == N {
      result := true;
      w := i;
      break;
    } else {
      i := i + 1;
    }
  }
  if result {
    assert w * w == N;
  } else {
    assert i == N + 1;
    assert forall j: nat :: j <= N ==> j * j != N;
  }
}

// </vc-code>
