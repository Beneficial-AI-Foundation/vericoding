// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM Main
method Main()
{
    M0();
    M1();
    EqualityOfStrings0();
    EqualityOfStrings1();
    M2();
    M3();
}

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

//ATOM M0
method M0()
{
    var s0 := [1, 2, 3];
    var s1 := [1, 2, 3];
    assert s0 == s1;
}

//ATOM M1
method M1()
{
    var s0 := [1, 2];
    var s1 := [1, 2, 3];
    assert s0 != s1;
}

//ATOM EqualityOfStrings0
method EqualityOfStrings0()
{
    var s0 := "hello";
    var s1 := "hello";
    assert s0 == s1;
}

//ATOM EqualityOfStrings1
method EqualityOfStrings1()
{
    var s0 := "hello";
    var s1 := "world";
    assert s0 != s1;
}

//ATOM M2
method M2()
{
    var s0 := [1, 2];
    var s1 := [3, 4];
    assert s0 + s1 == [1, 2, 3, 4];
}

//IMPL M3
method M3()
{
}