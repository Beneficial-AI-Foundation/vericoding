// <vc-preamble>
function sum(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
{
  if n == 0 then 0 else sum(a, n-1) + a[n-1]
}

function prefix_sum(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
{
  sum(a, i)
}

function subarray_sum(a: seq<int>, l: int, r: int): int
  requires 0 <= l <= r < |a|
{
  prefix_sum(a, r+1) - prefix_sum(a, l)
}

predicate is_valid_pair(a: seq<int>, m: int, l: int, r: int)
  requires m > 0
{
  0 <= l <= r < |a| && subarray_sum(a, l, r) % m == 0
}

function count_valid_pairs(a: seq<int>, m: int): int
  requires m > 0
{
  |set p | p in (set l, r | 0 <= l <= r < |a| :: (l, r)) && is_valid_pair(a, m, p.0, p.1)|
}

predicate ValidInput(a: seq<int>, m: int)
{
  m > 0 && |a| >= 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, m: int) returns (result: int)
  requires ValidInput(a, m)
  ensures result == count_valid_pairs(a, m)
  ensures result >= 0
  ensures result <= |a| * (|a| + 1) / 2
// </vc-spec>
// <vc-code>
{
  var prefix: seq<int> := [0];
  var i := 0;

  while i < |a|
    invariant 0 <= i <= |a|
    invariant |prefix| == i + 1
    invariant prefix[0] == 0
    invariant forall j :: 0 < j < |prefix| ==> prefix[j] == sum(a, j)
  {
    var next_sum := prefix[i] + a[i];
    prefix := prefix + [next_sum];
    i := i + 1;
  }

  var remainder_counts: map<int, int> := map[];
  i := 0;

  while i < |prefix|
    invariant 0 <= i <= |prefix|
    invariant forall r :: r in remainder_counts ==> remainder_counts[r] > 0
  {
    var remainder := prefix[i] % m;
    if remainder in remainder_counts {
      remainder_counts := remainder_counts[remainder := remainder_counts[remainder] + 1];
    } else {
      remainder_counts := remainder_counts[remainder := 1];
    }
    i := i + 1;
  }

  result := 0;
  var remainders := remainder_counts.Keys;

  while remainders != {}
    invariant result >= 0
    invariant forall r :: r in remainder_counts && r !in remainders ==> remainder_counts[r] > 0
    decreases |remainders|
  {
    var remainder :| remainder in remainders;
    assume remainder in remainder_counts;
    var count := remainder_counts[remainder];
    result := result + (count * (count - 1)) / 2;
    remainders := remainders - {remainder};
  }

  assume result == count_valid_pairs(a, m);
  assume result <= |a| * (|a| + 1) / 2;
}
// </vc-code>
