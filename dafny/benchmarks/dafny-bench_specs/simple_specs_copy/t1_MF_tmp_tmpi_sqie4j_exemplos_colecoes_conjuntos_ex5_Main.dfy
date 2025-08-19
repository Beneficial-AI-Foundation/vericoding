// SPEC

method Main() {
 var a: array<int> := new int[2];
 a[0] := 2;
 a[1] := 3;

 var ms: multiset<int> := multiset(a[..]);
}
