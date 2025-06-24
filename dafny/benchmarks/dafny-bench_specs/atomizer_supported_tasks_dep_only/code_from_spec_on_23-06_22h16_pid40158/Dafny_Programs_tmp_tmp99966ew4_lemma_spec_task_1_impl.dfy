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
   {
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
      invariant 0 <= i <= a.Length
      /* code modified by LLM (iteration 2): invariant to track that all checked positions are non-zero */
      invariant forall k :: 0 <= k < i ==> a[k] != 0
      /* code modified by LLM (iteration 2): invariant to handle skipped elements properly */
      invariant forall k :: 0 <= k < i ==> (k + a[k] <= i || k + a[k] >= a.Length)
      decreases a.Length - i
   {
      if a[i] == 0 {
         index := i;
         return;
      } else {
         assert a[i] > 0;
         /* code modified by LLM (iteration 2): apply SkippingLemma to establish properties of skipped range */
         SkippingLemma(a, i);
         /* code modified by LLM (iteration 2): assert what we learned from the lemma */
         assert forall k :: i <= k < i + a[i] && k < a.Length ==> a[k] != 0;
         
         /* code modified by LLM (iteration 2): skip by a[i] positions with proper bounds checking */
         var next := i + a[i];
         if next <= a.Length {
            i := next;
         } else {
            /* code modified by LLM (iteration 2): when skipping exceeds bounds, we can conclude no zeros exist */
            assert i + a[i] > a.Length;
            assert forall k :: i <= k < a.Length ==> a[k] != 0;
            /* code modified by LLM (iteration 2): establish that all elements have been effectively checked */
            assert forall k :: 0 <= k < a.Length ==> a[k] != 0;
            break;
         }
      }
   }
   /* code modified by LLM (iteration 2): when loop exits normally, all elements are non-zero */
   index := -1;
}