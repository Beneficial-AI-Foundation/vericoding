// SPEC
//ensures forall a, b :: 0 <= a < b < |s| ==> forall k, j :: a <=k < j <=b ==> k !=j ==> s[k] != s[j] ==> b-a <= longest
// lemma stringSet(s: string)
//  
//  {
//   if |s| != 0 {


//   }
//  }


method Main() {
	var sample: string := "test";
	var foof := Foo(3,4);
 	var test: set<char> := stringToSet(sample);
 	// var test := set x | 0 <= x < |sample| :: sample[x];
	print foof;
}
