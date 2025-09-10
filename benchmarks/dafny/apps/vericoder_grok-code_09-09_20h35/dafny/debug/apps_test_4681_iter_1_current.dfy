function Lucas(n: int): int
    requires n >= 0
{
    if n == 0 then 2
    else if n == 1 then 1
    else Lucas(n-1) + Lucas(n-2)
}

predicate ValidInput(n: int) {
    1 <= n <= 86
}

// <vc-helpers>
// No helpers needed for this implementation.
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
  decreases n;
  if n == 1 {
    result := 1;
  } else {
    var a := solve(n-1);
    var b := solve(n-2);
    result := a + b;
  }
}
// </vc-code>

