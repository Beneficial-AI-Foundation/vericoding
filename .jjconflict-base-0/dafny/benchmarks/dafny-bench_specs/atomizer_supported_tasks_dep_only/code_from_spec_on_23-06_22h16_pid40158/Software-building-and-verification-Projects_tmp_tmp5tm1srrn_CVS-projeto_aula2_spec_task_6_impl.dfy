//ATOM ATOM_PLACEHOLDER_max
method max(a: int, b: int) returns (result: int)
{
    if a >= b {
        result := a;
    } else {
        result := b;
    }
}

//ATOM ATOM_PLACEHOLDER_Main
method Main()
{
    print "Hello, World!\n";
}

//ATOM ATOM_PLACEHOLDER_mystery1
method mystery1(x: int) returns (y: int)
{
    y := x + 1;
}

//ATOM ATOM_PLACEHOLDER_mystery2
method mystery2(x: int) returns (y: int)
{
    y := x * 2;
}

//ATOM ATOM_PLACEHOLDER_m1
method m1(x: int) returns (y: int)
{
    y := x;
}

//IMPL m2
method m2(x: nat) returns (y: int)
  requires x <= -1
  ensures y > x && y < x
{
    // The precondition x <= -1 is impossible for nat (x >= 0)
    // So this method body will never execute
    y := 0;
}

//ATOM ATOM_PLACEHOLDER_m3
method m3(a: bool, b: bool) returns (result: bool)
{
    result := a == b;
}

//ATOM ATOM_PLACEHOLDER_m4
method m4(x: int) returns (y: int)
{
    y := x - 1;
}