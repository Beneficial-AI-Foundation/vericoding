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
// No helpers needed
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
  var a := 2; // Lucas(0)
  var b := 1; // Lucas(1)
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant a == Lucas(i - 1)
    invariant b == Lucas(i)
    decreases n - i
  {
    var next := a + b;
    a := b;
    b := next;
    i := i + 1;
  }
  result := b;
}
// </vc-code>

