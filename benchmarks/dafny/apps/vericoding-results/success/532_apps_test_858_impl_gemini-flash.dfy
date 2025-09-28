// <vc-preamble>
predicate IsPowerOfTwo(n: int) 
    decreases n
{
    if n <= 0 then false
    else if n == 1 then true
    else if n % 2 == 1 then false
    else IsPowerOfTwo(n / 2)
}

predicate ValidInput(n: int) {
    n >= 1
}

predicate CorrectResult(n: int, result: int) {
    if n % 2 == 1 then 
        result == (n - 1) / 2
    else 
        exists z :: 1 <= z <= n && IsPowerOfTwo(z) && z <= n && z * 2 > n && result == (n - z) / 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no change, was already correct */
predicate exists_z_such_that_z_is_max_power_of_2_le_n(n: int, z: int)
  requires n >= 1
{
  1 <= z <= n && IsPowerOfTwo(z) && z * 2 > n
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures CorrectResult(n, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added invariant to verify `z <= n` when constructing `result` */
{
  if n % 2 == 1 {
    result := (n - 1) / 2;
  } else {
    var z := 1;
    while z * 2 <= n
      invariant 1 <= z
      invariant IsPowerOfTwo(z)
      invariant z <= n
      invariant z * 2 <= n ==> forall k | 1 <= k && k < z && IsPowerOfTwo(k) :: k * 2 <= n
    {
      z := z * 2;
    }
    result := (n - z) / 2;
  }
}
// </vc-code>
