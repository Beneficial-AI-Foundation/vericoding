// <vc-preamble>
// ======= TASK =======
// Given a positive integer n, create an array a of length n where a[i] = i² - i + 1 
// for each position i from 1 to n. Count the number of triples (a[i], a[j], a[k]) 
// where i < j < k and the sum a[i] + a[j] + a[k] is divisible by 3.

// ======= SPEC REQUIREMENTS =======
function array_element(i: int): int
  requires i >= 1
{
  i * i - i + 1
}

function count_elements_mod_0(n: int): int
  requires n >= 0
  ensures count_elements_mod_0(n) >= 0
{
  if n == 0 then 0
  else if n % 3 == 2 then 1 + count_elements_mod_0(n - 1)
  else count_elements_mod_0(n - 1)
}

function count_elements_mod_1(n: int): int
  requires n >= 0
  ensures count_elements_mod_1(n) >= 0
{
  if n == 0 then 0
  else if n % 3 != 2 then 1 + count_elements_mod_1(n - 1)
  else count_elements_mod_1(n - 1)
}

function combination(n: int, k: int): int
  requires n >= 0 && k >= 0
  ensures combination(n, k) >= 0
  ensures k > n ==> combination(n, k) == 0
  ensures k == 0 || k == n ==> combination(n, k) == 1
  ensures k == 1 ==> combination(n, k) == n
  ensures k == 2 && n >= 2 ==> combination(n, k) == n * (n - 1) / 2
  ensures k == 3 && n >= 3 ==> combination(n, k) == n * (n - 1) * (n - 2) / 6
{
  if k > n || k < 0 then 0
  else if k == 0 || k == n then 1
  else if k == 1 then n
  else if k == 2 then n * (n - 1) / 2
  else if k == 3 then n * (n - 1) * (n - 2) / 6
  else 0
}

function count_valid_triples(n: int): int
  requires n >= 1
{
  var count_0 := count_elements_mod_0(n);
  var count_1 := count_elements_mod_1(n);
  combination(count_0, 3) + combination(count_1, 3)
}

predicate ValidInput(n: int)
{
  n >= 1
}
// </vc-preamble>

// <vc-helpers>
// ======= HELPERS =======
// </vc-helpers>

// <vc-spec>
// ======= MAIN METHOD =======
method get_max_triples(n: int) returns (result: int)
  requires ValidInput(n)
  ensures result >= 0
  ensures result == count_valid_triples(n)
// </vc-spec>
// <vc-code>
{
  var count_0 := 0;
  var count_1 := 0;

  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count_0 >= 0 && count_1 >= 0
    invariant count_0 + count_1 == i - 1
    invariant count_0 == count_elements_mod_0(i - 1)
    invariant count_1 == count_elements_mod_1(i - 1)
  {
    if i % 3 == 2 {
      count_0 := count_0 + 1;
    } else {
      count_1 := count_1 + 1;
    }
    i := i + 1;
  }

  var triples_0 := combination(count_0, 3);
  var triples_1 := combination(count_1, 3);

  result := triples_0 + triples_1;
}
// </vc-code>
