function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
lemma {:auto} FibRec(i: nat)
  requires i >= 3
  ensures fibfib(i) == fibfib(i-1) + fibfib(i-2) + fibfib(i-3)
{
  // Unfold definition of fibfib and use that i >= 3 selects the else branch.
  assert fibfib(i) == (if i == 0 || i == 1 then 0 else if i == 2 then 1 else fibfib(i-1) + fibfib(i-2) + fibfib(i-3));
  assert fibfib(i) == fibfib(i-1) + fibfib(i-2) + fibfib(i-3);
}
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == fibfib(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n == 0 || n == 1 {
    result := 0;
    return;
  }
  if n == 2 {
    result := 1;
    return;
  }

  var i := 3;
  var t0: nat := 0;
  var t1: nat := 0;
  var t2: nat := 1;
  while i <= n
    decreases n - i
    invariant 3 <= i <= n + 1
    invariant t0 == fibfib(i-3) && t1 == fibfib(i-2) && t2 == fibfib(i-1)
  {
    var next := t0 + t1 + t2;
    FibRec(i);
    assert next == fibfib(i);
    t0 := t1;
    t1 := t2;
    t2 := next;
    i := i + 1;
  }
  result := t2;
}
// </vc-code>

