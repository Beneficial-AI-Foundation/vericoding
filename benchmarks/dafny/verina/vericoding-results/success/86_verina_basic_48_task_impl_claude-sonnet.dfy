// <vc-preamble>
ghost predicate IsPerfectSquare(n: nat)
{
    exists i: nat :: i * i == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemma to prove perfect square properties and zero case */
lemma PerfectSquareProperties(n: nat, i: nat)
  requires i * i > n
  requires forall j: nat :: j < i ==> j * j != n
  ensures !IsPerfectSquare(n)
{
  if IsPerfectSquare(n) {
    var k: nat :| k * k == n;
    if k < i {
      assert k * k != n;
      assert false;
    } else {
      assert k >= i;
      assert k * k >= i * i > n;
      assert false;
    }
  }
}

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
  /* code modified by LLM (iteration 3): Fixed zero case and added proper lemma calls */
  if n == 0 {
    ZeroIsPerfectSquare();
    result := true;
    return;
  }
  
  var i := 1;
  while i * i <= n
    invariant i >= 1
    invariant forall j: nat :: j < i ==> j * j != n
  {
    if i * i == n {
      result := true;
      return;
    }
    i := i + 1;
  }
  
  PerfectSquareProperties(n as nat, i);
  result := false;
}
// </vc-code>
