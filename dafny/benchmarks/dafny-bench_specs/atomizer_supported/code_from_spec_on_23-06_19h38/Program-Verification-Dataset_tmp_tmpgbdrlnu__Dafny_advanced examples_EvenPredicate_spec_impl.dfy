// RUN: /compile:0 /nologo

//ATOM IsEven
function IsEven(a : int) : bool
    requires a >= 0
{
    if a == 0 then      true 
    else if a == 1 then false 
    else                IsEven(a - 2)
}

//ATOM EvenSquare
lemma EvenSquare(a : int)
requires a >= 0
ensures IsEven(a) ==> IsEven(a * a)
{
    if a >= 2 && IsEven(a) {
        EvenSquare(a - 2);
        EvenDouble(2 * a - 2);
        EvenPlus((a - 2) * (a - 2), 4 * a - 4);
    }
}

//ATOM EvenDouble
lemma EvenDouble(a: int)
    requires a >= 0
    ensures IsEven(a + a)
{
    if a >= 2 {
        EvenDouble(a - 2);
    }
}

//ATOM EvenPlus
lemma EvenPlus(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x + y)
{
    if x >= 2 {
        EvenPlus(x - 2, y);
    }
}

//ATOM Check1
lemma Check1(y: int)
    requires y >= 0
    ensures IsEven(2 * y)
{
    EvenDouble(y);
}

//ATOM EvenTimes
lemma EvenTimes(x: int, y: int)
    requires x >= 0
    requires y >= 0
    requires IsEven(x)
    requires IsEven(y)
    ensures IsEven(x * y)
{
    if x >= 2 {
        EvenTimes(x - 2, y);
        Check1(y);
        EvenPlus((x - 2) * y, 2 * y);
    }
}