
// SPEC 

method Foo(y: int, x: int) returns (z: int) 
  requires 0 <= y
  ensures z == x*y
{
}


//ATOM_PLACEHOLDER_stringToSet
//ensures forall a, b :: 0 <= a < b < |s|  ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
// lemma stringSet(s: string)
//    
//   {
//     if |s| != 0 {


//     }
//   }


//ATOM_PLACEHOLDER_Main

