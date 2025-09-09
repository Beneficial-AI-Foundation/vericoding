/*
// http://verifythus.cost-ic0701.org/common-example/arraymax-in-dafny

//max is larger then anything in the array

//max is an element in the array
*/

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method max(a:array<int>) returns(max:int)
    requires a != null;
    ensures forall j :: j >= 0 && j < a.Length ==> max >= a[j];
    ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a[j];
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
