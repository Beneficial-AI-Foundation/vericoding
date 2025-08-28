// <vc-helpers>
lemma PopcountBitwise(n: nat)
  ensures popcount(n) == popcount(n / 2) + (n % 2)
{
  if n == 0 {
    assert popcount(n) == 0;
    assert popcount(n / 2) + (n % 2) == popcount(0) + 0 == 0;
  } else {
    assert popcount(n) == n % 2 + popcount(n / 2);
    assert popcount(n / 2) + (n % 2) == n % 2 + popcount(n / 2);
  }
}

lemma PopcountMonotonic(n: nat)
  ensures n > 0 ==> popcount(n / 2) < popcount(n) || (popcount(n / 2) == popcount(n) && n % 2 == 0)
{
  if n > 0 {
    PopcountBitwise(n);
    assert popcount(n) == popcount(n / 2) + (n % 2);
  }
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
  r := 0;
  var temp := n;
  
  while temp > 0
    invariant r + popcount(temp) == popcount(n)
    decreases temp
  {
    PopcountBitwise(temp);
    r := r + (temp % 2);
    temp := temp / 2;
  }
  
  assert temp == 0;
  assert popcount(0) == 0;
  assert r + 0 == popcount(n);
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end