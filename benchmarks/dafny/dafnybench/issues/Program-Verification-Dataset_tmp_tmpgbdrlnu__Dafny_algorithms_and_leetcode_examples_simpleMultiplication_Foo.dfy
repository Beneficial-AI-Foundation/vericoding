// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Foo(y: int, x: int) returns (z: int) 
  requires 0 <= y
  ensures z == x*y
// </vc-spec>
// <vc-code>
{
  var a: int := 0;
  z := 0;
  while a != y 
   invariant 0 <= a <= y
   invariant z == a*x
   decreases y-a
  {
    z := z + x;
    a := a + 1;
  }
  return z;
}
// </vc-code>

function stringToSet(s: string): (r: set<char>)
ensures forall x :: 0 <= x < |s| ==> s[x] in r
{
 set x | 0 <= x < |s| :: s[x]
}
//ensures forall a, b :: 0 <= a < b < |s|  ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
// lemma stringSet(s: string)
//    
//   {
//     if |s| != 0 {


//     }
//   }