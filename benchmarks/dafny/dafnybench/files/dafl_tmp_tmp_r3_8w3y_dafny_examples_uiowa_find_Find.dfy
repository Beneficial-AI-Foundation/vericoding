// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;

   ensures 0 <= i ==> (
                       i < a.Length && 

                       a[i] == key && 

                       forall k :: 0 <= k < i ==> a[k] != key
                      );

   ensures i < 0 ==> 

           forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
