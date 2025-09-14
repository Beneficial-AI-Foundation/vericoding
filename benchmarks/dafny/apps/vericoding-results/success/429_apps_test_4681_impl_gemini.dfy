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

// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    return 1;
  }
  // For n >= 2, since ValidInput(n) implies 1 <= n.
  var i := 2;
  var prev := 2; // Lucas(0)
  var curr := 1; // Lucas(1)
  
  while i <= n
    invariant 2 <= i <= n + 1
    invariant prev == Lucas(i-2)
    invariant curr == Lucas(i-1)
  {
    var next_val := prev + curr;
    prev := curr;
    curr := next_val;
    i := i + 1;
  }
  
  return curr;
}
// </vc-code>

