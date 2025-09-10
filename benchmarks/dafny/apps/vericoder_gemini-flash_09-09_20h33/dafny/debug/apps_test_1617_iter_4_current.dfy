function f(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisor(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
function g(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisorHelper(d: int, n: int)
{
  d > 0 && n % d == 0
}

lemma SumOfArithmeticSeries(k: int)
  ensures (k * (k - 1) / 2) == (if k <= 0 then 0 else (k - 1) * k / 2)
{
  // This is a standard arithmetic series sum property.
  // Although the ensures clause is trivial for positive k, Dafny might need hints for k <= 0.
  // No explicit proof steps needed in Dafny for this triviality if used correctly.
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// Helper function to sort and remove duplicates from a sequence
function sortedDistinct(s: seq<int>): seq<int>
  ensures IsSorted(sortedDistinct(s))
  ensures NoDuplicates(sortedDistinct(s))
  ensures forall x :: x in sortedDistinct(s) <==> x in s
{
  if |s| <= 1 then s
  else
    var pivot := s[0];
    var smaller := sortedDistinct([x | x <- s[1..], x < pivot]);
    var larger := sortedDistinct([x | x <- s[1..], x > pivot]);
    var equal_elements := [x | x <- s, x == pivot];
    smaller + (if |equal_elements| > 0 then [pivot] else []) + larger // keep only one instance of pivot, ensures only `pivot` appears if it was in `s`
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires n >= 2
  ensures NoDuplicates(result)
  ensures IsSorted(result)
  ensures forall v :: v in result <==> exists d :: IsDivisor(d, n) && v == f(n, d)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  var divisors: seq<int> := [];
  var d := 1;
  while d * d <= n
    invariant d >= 1
    invariant forall d' :: 1 <= d' < d && d' * d' <= n ==> IsDivisor(d', n) ==> d' in divisors || (n/d') in divisors
    invariant forall d' :: 1 <= d' < d && IsDivisor(d', n) && d' * d' < n ==> d' in divisors && (n/d') in divisors
    invariant forall i :: 0 <= i < |divisors| ==> IsDivisor(divisors[i], n)
    invariant forall i, j :: 0 <= i < j < |divisors| ==> divisors[i] != divisors[j] // NoDuplicates(divisors)
    invariant forall x :: x in divisors ==> 1 <= x <= n && IsDivisor(x, n)
  {
    if n % d == 0 {
      if !(d in divisors) { // Ensure no duplicates are added
          divisors := divisors + [d];
      }
      if d * d != n {
        if !((n / d) in divisors) { // Ensure no duplicates are added
          divisors := divisors + [n / d];
        }
      }
    }
    d := d + 1;
  }

  // Calculate f(n,d) for each divisor
  var f_values: seq<int> := [];
  for i := 0 to |divisors| - 1
    invariant 0 <= i <= |divisors|
    invariant forall k :: 0 <= k < i ==> f_values[k] == f(n, divisors[k])
    invariant forall k :: 0 <= k < i ==> f_values[k] in f_values // This invariant is not useful as it tautological.
    invariant |f_values| == i
  {
    f_values := f_values + [f(n, divisors[i])];
  }

  // Sort and remove duplicates
  result := sortedDistinct(f_values);
}
// </vc-code>

