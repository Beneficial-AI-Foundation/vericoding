//ATOM

method M1()
{
}


//ATOM

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
}


//ATOM

method EqualityOfStrings0() {
}


//ATOM

method EqualityOfStrings1() {
}


// SPEC
// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
 M0();
 M1();
 EqualityOfStrings0();
 EqualityOfStrings1();
}
