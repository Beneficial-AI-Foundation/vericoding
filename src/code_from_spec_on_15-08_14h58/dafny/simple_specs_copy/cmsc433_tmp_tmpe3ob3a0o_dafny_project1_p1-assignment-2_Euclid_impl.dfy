// if and only if i % j == 0 (% is the Dafny mod operator). Write requires and
// ensures clauses for the method header Euclid below. Your requires clauses
// should also specify that the first argument is at least as large as the second.
// You do *not* need to implement the method!

/* code modified by LLM (iteration 4): Added GCD function definition */
function gcd(x: int, y: int): int
  requires x > 0 && y >= 0
  decreases y
{
  if y == 0 then x else gcd(y, x % y)
}

method Euclid (m : int, n : int) returns (result : int)
  requires m > 1 && n > 1 && m >= n
  ensures result > 0 && result <= n && result <= m && m % result == 0 && n % result == 0
{
  var a := m;
  var b := n;
  
  while b != 0
    invariant b >= 0
    invariant a > 0
    /* code modified by LLM (iteration 4): Fixed name conflict by renaming return variable */
    invariant gcd(m, n) == gcd(a, b)
    /* code modified by LLM (iteration 4): Added bound invariants */
    invariant a <= m + n
    invariant b < a || b == 0
    decreases b
  {
    var temp := a % b;
    /* code modified by LLM (iteration 4): Added assertions to help verification */
    assert temp >= 0 && temp < b;
    assert gcd(a, b) == gcd(b, temp);
    a := b;
    b := temp;
  }
  
  /* code modified by LLM (iteration 4): Added final assertions */
  assert b == 0;
  assert gcd(m, n) == gcd(a, 0);
  assert gcd(a, 0) == a;
  assert a > 0;
  assert a <= m && a <= n;
  
  /* code modified by LLM (iteration 4): Updated return assignment */
  result := a;
}