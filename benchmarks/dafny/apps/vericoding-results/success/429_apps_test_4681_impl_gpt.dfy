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
lemma LucasRec(n: int)
    requires n >= 2
    ensures Lucas(n) == Lucas(n-1) + Lucas(n-2)
{
    assert n != 0 && n != 1;
    assert Lucas(n) == (if n == 0 then 2 else if n == 1 then 1 else Lucas(n-1) + Lucas(n-2));
    assert Lucas(n) == Lucas(n-1) + Lucas(n-2);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
  var a := 2;
  var b := 1;
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant a == Lucas(i - 2)
    invariant b == Lucas(i - 1)
    decreases n - i + 1
  {
    var next := a + b;
    LucasRec(i);
    assert next == Lucas(i);
    a := b;
    b := next;
    i := i + 1;
  }
  result := b;
}
// </vc-code>

