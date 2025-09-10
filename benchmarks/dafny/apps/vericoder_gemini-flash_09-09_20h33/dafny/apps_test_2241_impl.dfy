function sum_contributions(a: seq<int>, b: seq<int>): int
    requires |a| == |b|
{
    if |a| == 0 then 0
    else 
        (if b[0] > 1 && 2 * a[0] >= b[0] then
            var x := b[0] / 2;
            var y := b[0] - x;
            x * y
         else -1) + sum_contributions(a[1..], b[1..])
}

// <vc-helpers>
function sum_contributions_iter(a: seq<int>, b: seq<int>, i: int, k: int): int
    requires 0 <= i <= k <= |a|
    requires |a| == |b|
    decreases k - i
{
    if i == k then 0
    else 
        (if b[i] > 1 && 2 * a[i] >= b[i] then
            var x := b[i] / 2;
            var y := b[i] - x;
            x * y
         else -1) + sum_contributions_iter(a, b, i + 1, k)
}
// This helper function is not strictly needed for the fix but can be used for proving equivalences.
predicate IsEqualToSumContributions(a: seq<int>, b: seq<int>, s: int)
    requires |a| == |b|
{
    s == sum_contributions(a, b)
}

// Another helper function, not strictly necessary but potentially useful for proving properties.
function sum_contributions_prefix(a: seq<int>, b: seq<int>, len: int): int
    requires 0 <= len <= |a|
    requires |a| == |b|
{
    sum_contributions_iter(a, b, 0, len)
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
   var n := |a|;
   var s := 0;
   for i := 0 to n
     invariant 0 <= i <= n
     invariant s == sum_contributions_iter(a, b, 0, i)
   {
     if i < n {
       if b[i] > 1 && 2 * a[i] >= b[i] {
         var x := b[i] / 2;
         var y := b[i] - x;
         s := s + x * y;
       } else {
         s := s + (-1); // Changed to s + (-1) for correctness
       }
     }
   }
   return s;
}
// </vc-code>

