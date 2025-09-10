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
  if exponent == 0 then (1 % modulus)
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
    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < i ==> 0 <= result_array[k] < MOD
      invariant forall k :: 0 <= k < i && k < n - 1 ==> result_array[k] == BlockCountFormula(n, k + 1)
      invariant forall k :: 0 <= k < i && k == n-1 ==> result_array[k] == 10
    {
      if i == n - 1 {
        result_array[i] := 10;
      } else {
        var term1: int := (2 * 9 * pow(10, n - i - 1, MOD) * 10) % MOD;
        var term2: int;
        if i < n - 1 { // i < n - 1 is true here since we are in the else branch and i < n - 1
            if i < n - 2 { // equivalent to n - 1 - i > 1
                term2 := ( (n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) % MOD;
            } else { // i == n - 2, so n - 1 - i == 1, n - i - 2 == 0
                term2 := 0; // Term is (n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10 when (n - 1 - i) is 1. If i == n - 2, this reduces to 9*9*pow(10,0,MOD)*10 = 810.
                          // The BlockCountFormula has 'if i < n-1 then ... else 0' part which corresponds to term2.
                          // When i = n-2, then (n - 1 - i) = 1. So it should be included.
                          // The condition `if i < n - 1 - 1` should be `if i < n - 1`, corresponding to original formula condition.
                          // No, the original BlockCountFormula for term2 says `if i < n - 1 then ..`.
                          // The `n - 1 - i` for `term2` implies that `n - 1 - i` can be 0 or 1.
                          // If `n - 1 - i` is 0, then i = n - 1, but this branch is `i < n - 1`.
                          // If `n - 1 - i` is 1, then i = n - 2. In this case, (n - 1 - i) is 1, so the term should be included.
                          // Thus, term2 is (1 * 9 * 9 * pow(10, 0, MOD) * 10) % MOD = 810 % MOD
                          // The BlockCountFormula's structure for the second term suggests that the term is 0 IF i >= n - 1.
                          // If i = n-2, which is less than n-1, the second term should be calculated.
                          // (n-1-i) * 9 * 9 * pow(10, n-i-2, MOD) * 10
                          // For i = n-2, this is (n-1-(n-2)) * 9 * 9 * pow(10, n-(n-2)-2, MOD) * 10
                          // = (1) * 9 * 9 * pow(10, 0, MOD) * 10 = 81 * 1 * 10 = 810.
                          // So, for i = n-2, term2 should be 810. It should not be 0.
                          // The condition `if i < n - 2` corresponds to `n - 1 - i > 1`.
                          // If `n - 1 - i == 1` (i.e., `i == n - 2`), the formula for `term2` uses `pow(10, 0, MOD)`.
                          // The structure of BlockCountFormula uses `i < n - 1`.
                          // So, `term2` applies if `i < n - 1`.
                            term2 := ((n - 1 - i) * 9 * 9 * pow(10, n - i - 2, MOD) * 10) % MOD;
                        }
        } else {
            term2 := 0; // This else branch means i >= n - 1. But main 'else' branch already covers `i < n - 1`. So, theoretically this branch is unreachable.
                      // Added to satisfy exhaustiveness of if-else.
        }
        result_array[i] := (term1 + term2) % MOD;
      }
      i := i + 1;
    }
  }
  result := result_array[..];
}
// </vc-code>

