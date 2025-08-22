// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//IMPL SPEC
// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
}


// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

//IMPL SPEC

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
}


//IMPL SPEC

method M1()
{
}


//IMPL SPEC

method EqualityOfStrings0() {
}


//IMPL SPEC

method EqualityOfStrings1() {
}


//IMPL SPEC

method M2()
{
}


//IMPL SPEC

method M3()
{
}