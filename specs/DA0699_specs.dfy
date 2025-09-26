// <vc-preamble>
function count(n: int, k: int): int
  requires n >= 0 && k >= 0
  ensures count(n, k) >= 0
{
  if n <= 0 then 0
  else countHelper(n, k, 0, 63, 0)
}
// </vc-preamble>

// <vc-helpers>
function countHelper(n: int, k: int, acc: int, b: int, c: int): int
  requires n >= 0 && k >= 0 && b >= -1 && c >= 0
  requires acc >= 0
  requires c <= k
  decreases b + 1
  ensures countHelper(n, k, acc, b, c) >= 0
{
  if b < 0 then 
    acc + (if bits(n) == k then 1 else 0)
  else if (n / power(2, b)) % 2 == 1 then
    if c < k then
      countHelper(n, k, acc + nck(b, k - c - 1), b - 1, c + 1)
    else
      countHelper(n, k, acc, b - 1, c)
  else
    countHelper(n, k, acc, b - 1, c)
}

function nck(n: int, k: int): int
  requires n >= 0 && k >= 0
  ensures nck(n, k) >= 0
{
  if k > n || k < 0 then 0
  else if k == 0 || k == n then 1
  else nck(n - 1, k - 1) + nck(n - 1, k)
}

function bits(n: int): int
  requires n >= 0
  ensures bits(n) >= 0
{
  if n == 0 then 0
  else (n % 2) + bits(n / 2)
}

function power(base: int, exp: int): int
  requires exp >= 0
  ensures exp == 0 ==> power(base, exp) == 1
  ensures base > 0 ==> power(base, exp) > 0
  ensures base == 0 && exp > 0 ==> power(base, exp) == 0
{
  if exp == 0 then 1
  else base * power(base, exp - 1)
}

function findHighestBit(n: int): int
  requires n > 0
  ensures findHighestBit(n) >= 0
{
  if n == 1 then 0
  else 1 + findHighestBit(n / 2)
}
// </vc-helpers>

// <vc-spec>
method solve(m: int, k: int) returns (result: int)
  requires m >= 0 && k >= 1 && k <= 64
  ensures result > 0 && result <= 1000000000000000000
  ensures count(2 * result, k) - count(result, k) >= m
  ensures result == 1 || count(2 * (result - 1), k) - count(result - 1, k) < m
// </vc-spec>
// <vc-code>
{
  var lo := 1;
  var hi := 1000000000000000000; // 10^18

  while lo < hi
    invariant 1 <= lo <= hi <= 1000000000000000000
    invariant lo == 1 || count(2 * (lo - 1), k) - count(lo - 1, k) < m
    invariant hi > 1000000000000000000 || count(2 * hi, k) - count(hi, k) >= m
  {
    var mi := (lo + hi) / 2;
    var count1 := count(2 * mi, k);
    var count2 := count(mi, k);
    var countResult := count1 - count2;
    if countResult < m {
      lo := mi + 1;
    } else {
      hi := mi;
    }
  }

  result := lo;
}
// </vc-code>
