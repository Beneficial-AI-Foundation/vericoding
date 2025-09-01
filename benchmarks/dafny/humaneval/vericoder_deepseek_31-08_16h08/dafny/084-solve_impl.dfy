

// <vc-helpers>
lemma popcount_lemma(n: nat)
  ensures popcount(n) == (if n == 0 then 0 else (n % 2) + popcount(n / 2))
{
  // This lemma is trivial since popcount is defined as a function
}

lemma popcount_div2_less(n: nat)
  requires n > 0
  ensures n / 2 < n
{
  // n/2 is always less than n when n > 0
  if n == 1 {
  } else {
    assert n / 2 <= n - 1 < n;
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
  if n == 0 {
    r := 0;
  } else {
    var half_count := solve(n / 2);
    r := (n % 2) + half_count;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end