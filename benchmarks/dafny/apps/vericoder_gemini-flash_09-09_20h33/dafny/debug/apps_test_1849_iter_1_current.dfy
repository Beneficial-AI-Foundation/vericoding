const MOD := 998244353

predicate ValidInput(n: int)
{
  n >= 1
}

function BlockCountFormula(n: int, i: int): int
  requires n >= 1 && 1 <= i <= n
{
  if i == n then 10
  else 
    ((2 * 9 * pow(10, n - i - 1, MOD) * 10) + 
     (if i < n - 1 then ((n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) else 0)) % MOD
}

predicate ValidResult(result: seq<int>, n: int)
  requires n >= 1
{
  |result| == n &&
  (forall k :: 0 <= k < n ==> 0 <= result[k] < MOD) &&
  (n >= 1 ==> result[n-1] == 10) &&
  (forall i :: 0 <= i < n-1 ==> result[i] == BlockCountFormula(n, i+1))
}

// <vc-helpers>
function pow(base: int, exponent: int, modulus: int): int
  requires exponent >= 0 && modulus > 0
  ensures 0 <= pow(base, exponent, modulus) < modulus
  decreases exponent
{
  if exponent == 0 then 1
  else (base * pow(base, exponent - 1, modulus)) % modulus
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires ValidInput(n)
  ensures ValidResult(result, n)
// </vc-spec>
// <vc-code>
{
  var result_array: array<int>;
  if n == 1 {
    result_array := new int[1];
    result_array[0] := 10;
  } else {
    result_array := new int[n];
    var i := 0;
    while i < n {
      if i == n - 1 {
        result_array[i] := 10;
      } else {
        var term1: int := (2 * 9 * pow(10, n - i - 1, MOD) * 10) % MOD;
        var term2: int;
        if i < n - 1 - 1 { // i < n - 2
          term2 := ((n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) % MOD;
        } else {
          term2 := 0;
        }
        result_array[i] := (term1 + term2) % MOD;
      }
      i := i + 1;
    }
  }
  result := result_array[..];
}
// </vc-code>

