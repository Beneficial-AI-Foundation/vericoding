predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

// <vc-helpers>
lemma multipleGcd(n: int, a: int, b: int, p: int, q: int, x: int)
  requires ValidInput(n, a, b, p, q)
  requires x >= 0
  ensures p * (x / a) + q * (x / b) - q * (x / (a * b / gcd(a, b))) >= 0
{
}

lemma inclusionExclusion(n: int, a: int, b: int, x: int)
  requires a > 0 && b > 0 && x >= 0
  ensures x / a + x / b - x / (a * b / gcd(a, b)) == x / a + x / b - x / lcm(a, b)
{
}

function lcm(a: int, b: int): int
  requires a > 0 && b > 0
{
  a * b / gcd(a, b)
}

lemma monotonicSearch(n: int, a: int, b: int, p: int, q: int, low: int, high: int)
  requires ValidInput(n, a, b, p, q)
  requires 0 <= low <= high
  requires p * (low / a) + q * (low / b) - q * (low / lcm(a, b)) < n
  requires p * (high / a) + q * (high / b) - q * (high / lcm(a, b)) >= n
  ensures exists x :: low <= x <= high && p * (x / a) + q * (x / b) - q * (x / lcm(a, b)) >= n
{
}

lemma binarySearchBounds(n: int, a: int, b: int, p: int, q: int) returns (upper: int)
  requires ValidInput(n, a, b, p, q)
  ensures upper >= 0
  ensures p * (upper / a) + q * (upper / b) - q * (upper / lcm(a, b)) >= n
{
  upper := n * max(p, q) * max(a, b);
  multipleGcd(n, a, b, p, q, upper);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var lcm_ab := a * b / gcd(a, b);
  var low := 0;
  var high := binarySearchBounds(n, a, b, p, q);
  
  while low < high
    invariant 0 <= low <= high
    invariant p * (low / a) + q * (low / b) - q * (low / lcm_ab) < n
    invariant p * (high / a) + q * (high / b) - q * (high / lcm_ab) >= n
  {
    var mid := (low + high) / 2;
    var count := p * (mid / a) + q * (mid / b) - q * (mid / lcm_ab);
    
    if count < n {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  result := high;
}
// </vc-code>

