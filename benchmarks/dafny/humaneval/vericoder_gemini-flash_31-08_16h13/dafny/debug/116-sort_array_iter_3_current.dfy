function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}

// <vc-helpers>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
   if |s| == 0 then {
     return [];
   }
   var a := new nat[|s|];
   for i := 0 to |s| - 1
     invariant 0 <= i <= |s|
     invariant forall j :: 0 <= j < i ==> a[j] == s[j]
   {
     a[i] := s[i];
   }

   // Bubble sort based on popcount
   for i := 0 to |a| - 2
     invariant 0 <= i < |a|
     invariant forall x, y :: 0 <= x < y < i ==> popcount(a[x]) <= popcount(a[y])
     invariant multiset(a[..]) == multiset(s) // Elements are preserved
     // Ensure that the prefix is sorted up to i
     invariant forall k :: 0 <= k < i ==> (forall l :: k < l < |a| ==> popcount(a[k]) <= popcount(a[l]))
   {
     for j := |a| - 2 downto i
       invariant i <= j < |a|
       invariant multiset(a[..]) == multiset(s) // Elements are preserved
       invariant forall k :: 0 <= k < i ==> (forall l :: k < l < |a| ==> popcount(a[k]) <= popcount(a[l]))
       invariant forall x, y :: j+1 <= x < y < |a| ==> popcount(a[x]) <= popcount(a[y])
     {
       if popcount(a[j]) > popcount(a[j+1])
       {
         var temp := a[j];
         a[j] := a[j+1];
         a[j+1] := temp;
       }
     }
   }
   return a[..];
}
// </vc-code>

