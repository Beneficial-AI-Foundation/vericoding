// Given an array of positive and negative integers,
//  it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

//ATOM 
// Given an array of positive and negative integers,
//  it returns an array of the absolute value of all the integers. [-4,1,5,-2,-5]->[4,1,5,2,5]

function abs(x:int):nat {
    if x < 0 then -x else x
}

//IMPL absx
method absx(x:array<int>) returns (y:array<int>) 
ensures y.Length == x.Length
ensures forall i :: 0 <= i < y.Length ==>  y[i] == abs(x[i])
{
    y := new int[x.Length];
    var i := 0;
    while i < x.Length
        invariant 0 <= i <= x.Length
        invariant y.Length == x.Length
        invariant forall j :: 0 <= j < i ==> y[j] == abs(x[j])
    {
        y[i] := abs(x[i]);
        i := i + 1;
    }
}

//IMPL Main
method Main() {
    var input := new int[5];
    input[0] := -4;
    input[1] := 1;
    input[2] := 5;
    input[3] := -2;
    input[4] := -5;
    
    var result := absx(input);
    
    print "Input: [";
    var i := 0;
    while i < input.Length {
        print input[i];
        if i < input.Length - 1 { print ", "; }
        i := i + 1;
    }
    print "]\n";
    
    print "Output: [";
    i := 0;
    while i < result.Length {
        print result[i];
        if i < result.Length - 1 { print ", "; }
        i := i + 1;
    }
    print "]\n";
}