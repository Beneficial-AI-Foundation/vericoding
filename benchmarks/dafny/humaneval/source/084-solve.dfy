method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
{
  // impl-start
  var m := n;
  r := 0;
  while m > 0
    // invariants-start
    invariant r + popcount(m) == popcount(n)
    // invariants-end
  {
    r := r + m % 2;
    m := m / 2;
  }
  // impl-end
}

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end
