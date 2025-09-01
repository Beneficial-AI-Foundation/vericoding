

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method common(l1 : seq<int>, l2 : seq<int>) returns (c : set<int>)
   // post-conditions-start
    ensures forall i :: i in c ==> i in l1 && i in l2
    ensures forall i :: i in l1 && i in l2 ==> i in c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
   c := {};
   var i := 0;
   while i < |l1|
     invariant 0 <= i <= |l1|
     invariant forall x :: x in c ==> x in l1 && x in l2
     invariant forall x :: (exists j :: 0 <= j < i && l1[j] == x) && x in l2 ==> x in c
   {
     var j := 0;
     while j < |l2|
       invariant 0 <= j <= |l2|
       invariant forall x :: x in c ==> x in l1 && x in l2
       invariant forall x :: (exists k :: 0 <= k < i && l1[k] == x) && x in l2 ==> x in c
       invariant (l1[i] in c) == (l1[i] in l2[0..j] || (l1[i] in c && l1[i] in l2[0..j]))
     {
       if l1[i] == l2[j]
       {
         c := c + {l1[i]};
       }
       j := j + 1;
     }
     i := i + 1;
   }
   return c;
}
// </vc-code>

