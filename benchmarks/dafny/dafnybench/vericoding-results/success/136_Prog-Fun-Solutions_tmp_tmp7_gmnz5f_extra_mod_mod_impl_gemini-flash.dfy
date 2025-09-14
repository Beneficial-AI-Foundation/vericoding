ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

// <vc-helpers>
function F_memo(n: nat, memo: array<nat>): nat
  reads memo
  requires 0 <= n < memo.Length
  requires forall k :: 0 <= k < n ==> memo[k] == f(k)
{
  if n == 0 then 1
  else if n % 2 == 0 then 1 + 2 * memo[n / 2]
  else 2 * memo[n / 2]
}
// </vc-helpers>

// <vc-spec>
method mod(n:nat) returns (a:nat) 
ensures a == f(n)
// </vc-spec>
// <vc-code>
{
  if n == 0 {
    return 1;
  }

  var memo := new nat[n + 1];
  memo[0] := 1;

  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> memo[k] == f(k)
    invariant memo[0] == 1
  {
    if i % 2 == 0 {
      memo[i] := 1 + 2 * memo[i / 2];
      calc {
        f(i);
        { assert i/2 < i; }
        1 + 2 * f(i / 2);
        1 + 2 * memo[i / 2];
      }
    } else {
      memo[i] := 2 * memo[i / 2];
      calc {
        f(i);
        { assert i/2 < i; }
        2 * f(i / 2);
        2 * memo[i / 2];
      }
    }
    i := i + 1;
  }
  return memo[n];
}
// </vc-code>

