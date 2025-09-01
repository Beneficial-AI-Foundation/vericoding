

// <vc-helpers>
function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}

lemma PopcountProperty(n: nat)
  ensures popcount(n) == n % 2 + popcount(n / 2)
{
  if n == 0 {
    calc {
      popcount(n);
      == { assert n == 0; }
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
    assert cnt == popcount(half);
    var remainder := n % 2;
    calc {
      remainder + cnt;
      == 
        n % 2 + popcount(half);
      == { PopcountProperty(n); }
        popcount(n);
    }
    return remainder + cnt;
  }
}
// </vc-code>

function popcount(n: nat): nat {
  if n == 0 then 0 else n % 2 + popcount(n / 2)
}
// pure-end