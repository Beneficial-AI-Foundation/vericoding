

// <vc-helpers>
lemma PopcountStep(n: nat)
  ensures n > 0 ==> popcount(n) == n % 2 + popcount(n / 2)
{
  // This follows directly from the definition
}

lemma PopcountZero()
  ensures popcount(0) == 0
{
  // This follows directly from the definition
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat) returns (r: nat)
  // post-conditions-start
  ensures r == popcount(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var m := n;
  
  while m > 0
    invariant popcount(m) + count == popcount(n)
    decreases m
  {
    count := count + m % 2;
    m := m / 2;
  }
  
  r := count;
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end