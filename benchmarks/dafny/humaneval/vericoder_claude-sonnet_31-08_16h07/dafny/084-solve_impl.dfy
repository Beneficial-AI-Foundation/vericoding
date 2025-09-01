

// <vc-helpers>
lemma PopcountDecrease(n: nat)
  requires n > 0
  ensures popcount(n / 2) < popcount(n) || popcount(n / 2) == popcount(n)
  decreases n
{
  if n == 1 {
    assert popcount(1) == 1;
    assert popcount(0) == 0;
  } else if n > 1 {
    assert popcount(n) == n % 2 + popcount(n / 2);
    assert n % 2 >= 0;
  }
}

lemma PopcountBound(n: nat)
  ensures popcount(n) <= n
  decreases n
{
  if n == 0 {
    assert popcount(0) == 0;
  } else {
    PopcountBound(n / 2);
    assert popcount(n) == n % 2 + popcount(n / 2);
    assert n % 2 <= 1;
    assert popcount(n / 2) <= n / 2;
    assert popcount(n) <= 1 + n / 2;
    assert 1 + n / 2 <= n;
  }
}

lemma PopcountDivision(n: nat)
  ensures popcount(n) == n % 2 + popcount(n / 2)
{
  if n == 0 {
    assert popcount(0) == 0;
    assert 0 % 2 == 0;
    assert popcount(0 / 2) == 0;
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
  var temp: nat := n;
  
  while temp > 0
    invariant r + popcount(temp) == popcount(n)
    invariant temp <= n
    decreases temp
  {
    PopcountBound(temp);
    PopcountDivision(temp);
    if temp % 2 == 1 {
      r := r + 1;
    }
    temp := temp / 2;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end