

// <vc-helpers>
ghost method PopcountProperty(n: nat) returns (c: nat)
  ensures c == n % 2 + popcount(n / 2)
{
  if n == 0 {
    calc {
      0;
      == { assert n == 0; }
      n % 2 + popcount(n / 2);
    }
  } else {
    calc {
      popcount(n);
      == { assert n != 0; }
      n % 2 + popcount(n / 2);
    }
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
    return 0;
  } else {
    var half := n / 2;
    var cnt := solve(half);
    var remainder := n % 2;
    return remainder + cnt;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end