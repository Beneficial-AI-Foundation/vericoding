// ATOM 
lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
      invariant j <= i <= j + a[j]
      invariant i <= a.Length
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
   {
      assert j <= i < j + a[j] && i < a.Length;
      assert a[i] != 0 by {
         if i == j {
            assert a[j] > 0;
         } else {
            assert j < i;
            assert a[i-1] - 1 <= a[i];
            assert a[i-1] != 0;
            assert a[i] >= a[i-1] - 1 >= 0 - 1;
            assert a[i] >= 0;
            if a[i] == 0 {
               assert a[i-1] >= 1;
               assert i - 1 >= j;
               assert i - 1 < j + a[j];
               assert a[i-1] != 0;
               assert false;
            }
         }
      }
      i := i + 1;
   }
}

// IMPL FindZero
method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
{
   var i := 0;
   
   while i < a.Length
      /* code modified by LLM (iteration 1): fixed invariant to properly track skipped positions */
      invariant 0 <= i <= a.Length
      invariant forall k :: 0 <= k < i ==> a[k] != 0
   {
      if a[i] == 0 {
         index := i;
         return;
      } else {
         /* code modified by LLM (iteration 1): call lemma to establish skipping property */
         SkippingLemma(a, i);
         /* code modified by LLM (iteration 1): assert properties needed for invariant maintenance */
         assert a[i] > 0;
         assert forall k :: i <= k < i + a[i] && k < a.Length ==> a[k] != 0;
         /* code modified by LLM (iteration 1): update loop variable with skip amount */
         var next_i := i + a[i];
         /* code modified by LLM (iteration 1): assert that all skipped positions are non-zero */
         assert forall k :: i <= k < next_i && k < a.Length ==> a[k] != 0;
         i := next_i;
      }
   }
   
   /* code modified by LLM (iteration 1): assert postcondition before return */
   assert forall k :: 0 <= k < a.Length ==> a[k] != 0;
   index := -1;
}