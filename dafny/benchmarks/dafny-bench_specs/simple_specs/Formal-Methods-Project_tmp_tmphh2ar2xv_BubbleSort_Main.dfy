//ATOM

method BubbleSort(a: array?<int>)
 modifies a
 requires a != null
 {
}


// SPEC
 
method Main() {
 var a := new int[5];
 a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
 BubbleSort(a);
 var k := 0;
 while(k < 5) { print a[k], "\n"; k := k+1;}
}
