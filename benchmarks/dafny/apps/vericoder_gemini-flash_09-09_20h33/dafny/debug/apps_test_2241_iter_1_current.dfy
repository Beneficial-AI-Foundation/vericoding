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

// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>, b: seq<int>) returns (result: int)
    requires |a| == |b|
    ensures result == sum_contributions(a, b)
// </vc-spec>
// <vc-code>
{
   var n := |a>;
   var s := 0;
   for i := 0 to n
     invariant 0 <= i <= n
     invariant s == sum_contributions(a[0..i], b[0..i])
   {
     if i < n {
       if b[i] > 1 && 2 * a[i] >= b[i] then
         var x := b[i] / 2;
         var y := b[i] - x;
         s := s + x * y;
       else
         s := s - 1;
     }
   }
   return s;
}
// </vc-code>

