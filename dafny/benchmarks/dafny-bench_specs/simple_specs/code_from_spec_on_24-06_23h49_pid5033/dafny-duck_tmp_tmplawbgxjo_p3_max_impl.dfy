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