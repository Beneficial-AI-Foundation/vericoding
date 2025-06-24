//Given an array of natural numbers, it returns the maximum value. [5,1,3,6,12,3]->12

//IMPL 
//Given an array of natural numbers, it returns the maximum value. [5,1,3,6,12,3]->12

method max(x:array<nat>) returns (y:nat) 
// for index loop problems
requires x.Length > 0
// ensuring that we maintain y as greater than the elements in the array 
ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
// ensuring that the return value is in the array
ensures y in x[..]
{
    y := x[0];
    var i := 1;
    
    while i < x.Length
        invariant 1 <= i <= x.Length
        invariant forall j :: 0 <= j < i ==> y >= x[j]
        invariant y in x[0..i]
    {
        if x[i] > y {
            y := x[i];
        }
        i := i + 1;
    }
}

//IMPL 

method Main()
{
    var arr := new nat[6];
    arr[0] := 5;
    arr[1] := 1;
    arr[2] := 3;
    arr[3] := 6;
    arr[4] := 12;
    arr[5] := 3;
    
    var result := max(arr);
    print "Maximum value: ", result, "\n";
}