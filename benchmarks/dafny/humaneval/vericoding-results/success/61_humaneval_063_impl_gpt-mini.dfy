// <vc-preamble>

function fibfib_spec(n: int): int
    requires n >= 0
{
    if n == 0 then 0
    else if n == 1 then 0
    else if n == 2 then 1
    else fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
}
// </vc-preamble>

// <vc-helpers>
lemma fibfib_rec(i: int)
  requires i >= 3
  ensures fibfib_spec(i) == fibfib_spec(i-1) + fibfib_spec(i-2) + fibfib_spec(i-3)
{
  assert fibfib_spec(i) == fibfib_spec(i-1) + fibfib_spec(i-2) + fibfib_spec(i-3);
}

// </vc-helpers>

// <vc-spec>
method fibfib(n: int) returns (result: int)
    requires n >= 0
    ensures result == fibfib_spec(n)
    ensures n == 0 ==> result == 0
    ensures n == 1 ==> result == 0
    ensures n == 2 ==> result == 1
    ensures n >= 3 ==> result == fibfib_spec(n-1) + fibfib_spec(n-2) + fibfib_spec(n-3)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    result := 0;
    return;
  }
  if n == 1 {
    result := 0;
    return;
  }
  if n == 2 {
    result := 1;
    return;
  }
  var i := 3;
  var f3 := fibfib_spec(0);
  var f2 := fibfib_spec(1);
  var f1 := fibfib_spec(2);
  while i <= n
    invariant 3 <= i <= n+1
    invariant f3 == fibfib_spec(i-3)
    invariant f2 == fibfib_spec(i-2)
    invariant f1 == fibfib_spec(i-1)
  {
    var cur := f1 + f2 + f3;
    fibfib_rec(i);
    assert fibfib_spec(i) == fibfib_spec(i-1) + fibfib_spec(i-2) + fibfib_spec(i-3);
    assert fibfib_spec(i) == f1 + f2 + f3;
    assert cur == fibfib_spec(i);
    f3 := f2;
    f2 := f1;
    f1 := cur;
    i := i + 1;
  }
  result := f1;
}
// </vc-code>
